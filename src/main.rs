use anyhow::{Result, anyhow};
use cairo::ffi::{xcb_connection_t, xcb_visualtype_t};
use cairo::{Context, XCBConnection as CairoXCBConnection, XCBDrawable, XCBSurface, XCBVisualType};
use log::{debug, warn};
use pango::FontDescription;
use std::cell::{Cell, RefCell};
use std::env;
use std::io;
use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd, RawFd};
use std::time::Duration;
use xbar_core::linux::AlignedTimer;
use xbar_core::presentation::{Point, PointerAction, PresentationConfig, Size};
use xbar_core::render::cairo::CairoBar;
use xbar_core::{
    BarEffect, BarRuntime, ModelConfig, MonitorGeometry, NotifierChange, PlatformEffectHandler,
    RuntimeUpdate, TransportNotifierSlot, TransportRecoveryConfig,
};
use xbar_linux_actions::ProcessActionHandler;
use xcb::{self, Xid, x};

const X_TOKEN: u64 = 1;
const TIMER_TOKEN: u64 = 2;
const SHARED_TOKEN: u64 = 3;
const TRANSPORT_RETRY_INTERVAL: Duration = Duration::from_secs(2);

// ---------------- Cairo XCB bridge ----------------
struct CairoXcb {
    connection: CairoXCBConnection,
    visual: XCBVisualType,
    _visual_owner: Box<x::Visualtype>,
}

fn find_visual_by_id_and_depth(
    screen: &x::Screen,
    target_visual_id: u32,
    target_depth: u8,
) -> Option<x::Visualtype> {
    for depth in screen.allowed_depths() {
        if depth.depth() == target_depth {
            for visual in depth.visuals() {
                if visual.visual_id() == target_visual_id {
                    return Some(*visual);
                }
            }
        }
    }
    None
}

fn build_cairo_xcb(conn: &xcb::Connection, screen: &x::Screen) -> Result<CairoXcb> {
    let visual = find_visual_by_id_and_depth(screen, screen.root_visual(), screen.root_depth())
        .ok_or_else(|| anyhow!("could not find the root X visual"))?;
    let visual_owner = Box::new(visual);
    let visual_ptr = (&*visual_owner) as *const x::Visualtype as *mut xcb_visualtype_t;
    let visual = unsafe { XCBVisualType::from_raw_none(visual_ptr) };
    let raw_connection = conn.get_raw_conn();
    let connection =
        unsafe { CairoXCBConnection::from_raw_none(raw_connection.cast::<xcb_connection_t>()) };

    Ok(CairoXcb {
        connection,
        visual,
        _visual_owner: visual_owner,
    })
}

// ---------------- XCB back buffer ----------------
struct BackBuffer {
    pixmap: x::Pixmap,
    width: u16,
    height: u16,
    depth: u8,
    surface: Option<XCBSurface>,
    context: Option<Context>,
}

impl BackBuffer {
    fn new(
        conn: &xcb::Connection,
        screen: &x::Screen,
        win: x::Window,
        width: u16,
        height: u16,
    ) -> Result<Self> {
        let pixmap = conn.generate_id();
        conn.send_and_check_request(&x::CreatePixmap {
            depth: screen.root_depth(),
            pid: pixmap,
            drawable: x::Drawable::Window(win),
            width,
            height,
        })?;
        Ok(Self {
            pixmap,
            width,
            height,
            depth: screen.root_depth(),
            surface: None,
            context: None,
        })
    }

    fn ensure_context<'a>(&'a mut self, cairo_xcb: &CairoXcb) -> Result<&'a Context> {
        if self.surface.is_none() {
            let drawable = XCBDrawable(self.pixmap.resource_id());
            let surface = XCBSurface::create(
                &cairo_xcb.connection,
                &drawable,
                &cairo_xcb.visual,
                i32::from(self.width),
                i32::from(self.height),
            )?;
            let context = Context::new(&surface)?;
            self.surface = Some(surface);
            self.context = Some(context);
        }
        self.context
            .as_ref()
            .ok_or_else(|| anyhow!("Cairo context was not initialized"))
    }

    fn flush(&self) {
        if let Some(surface) = &self.surface {
            surface.flush();
        }
    }

    fn resize_if_needed(
        &mut self,
        conn: &xcb::Connection,
        win: x::Window,
        width: u16,
        height: u16,
    ) -> Result<()> {
        if self.width == width && self.height == height {
            return Ok(());
        }

        conn.send_and_check_request(&x::FreePixmap {
            pixmap: self.pixmap,
        })?;
        let pixmap = conn.generate_id();
        conn.send_and_check_request(&x::CreatePixmap {
            depth: self.depth,
            pid: pixmap,
            drawable: x::Drawable::Window(win),
            width,
            height,
        })?;
        self.pixmap = pixmap;
        self.width = width;
        self.height = height;
        self.surface = None;
        self.context = None;
        Ok(())
    }

    fn blit_to_window(
        &self,
        conn: &xcb::Connection,
        win: x::Window,
        gc: x::Gcontext,
    ) -> Result<()> {
        conn.send_and_check_request(&x::CopyArea {
            src_drawable: x::Drawable::Pixmap(self.pixmap),
            dst_drawable: x::Drawable::Window(win),
            gc,
            src_x: 0,
            src_y: 0,
            dst_x: 0,
            dst_y: 0,
            width: self.width,
            height: self.height,
        })?;
        Ok(())
    }
}

// ---------------- EWMH ----------------
struct Atoms {
    net_wm_window_type: x::Atom,
    net_wm_window_type_dock: x::Atom,
    net_wm_state: x::Atom,
    net_wm_state_above: x::Atom,
    net_wm_desktop: x::Atom,
    net_wm_strut_partial: x::Atom,
    net_wm_strut: x::Atom,
    net_wm_name: x::Atom,
    utf8_string: x::Atom,
    atom: x::Atom,
    cardinal: x::Atom,
}

fn intern_atom(conn: &xcb::Connection, name: &str) -> Result<x::Atom> {
    let cookie = conn.send_request(&x::InternAtom {
        only_if_exists: false,
        name: name.as_bytes(),
    });
    Ok(conn.wait_for_reply(cookie)?.atom())
}

fn intern_atoms(conn: &xcb::Connection) -> Result<Atoms> {
    Ok(Atoms {
        net_wm_window_type: intern_atom(conn, "_NET_WM_WINDOW_TYPE")?,
        net_wm_window_type_dock: intern_atom(conn, "_NET_WM_WINDOW_TYPE_DOCK")?,
        net_wm_state: intern_atom(conn, "_NET_WM_STATE")?,
        net_wm_state_above: intern_atom(conn, "_NET_WM_STATE_ABOVE")?,
        net_wm_desktop: intern_atom(conn, "_NET_WM_DESKTOP")?,
        net_wm_strut_partial: intern_atom(conn, "_NET_WM_STRUT_PARTIAL")?,
        net_wm_strut: intern_atom(conn, "_NET_WM_STRUT")?,
        net_wm_name: intern_atom(conn, "_NET_WM_NAME")?,
        utf8_string: intern_atom(conn, "UTF8_STRING")?,
        atom: intern_atom(conn, "ATOM")?,
        cardinal: intern_atom(conn, "CARDINAL")?,
    })
}

fn change_property_32(
    conn: &xcb::Connection,
    win: x::Window,
    property: x::Atom,
    property_type: x::Atom,
    data: &[u32],
) -> Result<()> {
    // Passing u32 values directly is significant: xcb derives the protocol
    // format from the element type, so this emits format=32 rather than the
    // format=8 request produced by the former byte conversion.
    conn.send_and_check_request(&x::ChangeProperty {
        mode: x::PropMode::Replace,
        window: win,
        property,
        r#type: property_type,
        data,
    })?;
    Ok(())
}

fn change_property_8(
    conn: &xcb::Connection,
    win: x::Window,
    property: x::Atom,
    property_type: x::Atom,
    data: &[u8],
) -> Result<()> {
    conn.send_and_check_request(&x::ChangeProperty {
        mode: x::PropMode::Replace,
        window: win,
        property,
        r#type: property_type,
        data,
    })?;
    Ok(())
}

fn update_strut(
    conn: &xcb::Connection,
    atoms: &Atoms,
    win: x::Window,
    x: i32,
    y: i32,
    width: u32,
    bar_height: u16,
) -> Result<()> {
    let top = u32::try_from(y)
        .unwrap_or(0)
        .saturating_add(u32::from(bar_height));
    let top_start_x = u32::try_from(x).unwrap_or(0);
    let top_end_x = top_start_x.saturating_add(width.saturating_sub(1));
    let strut_partial = [0, 0, top, 0, 0, 0, 0, 0, top_start_x, top_end_x, 0, 0];
    change_property_32(
        conn,
        win,
        atoms.net_wm_strut_partial,
        atoms.cardinal,
        &strut_partial,
    )?;
    change_property_32(
        conn,
        win,
        atoms.net_wm_strut,
        atoms.cardinal,
        &[0, 0, top, 0],
    )
}

fn set_dock_properties(
    conn: &xcb::Connection,
    atoms: &Atoms,
    win: x::Window,
    width: u32,
    bar_height: u16,
) -> Result<()> {
    change_property_32(
        conn,
        win,
        atoms.net_wm_window_type,
        atoms.atom,
        &[atoms.net_wm_window_type_dock.resource_id()],
    )?;
    change_property_32(
        conn,
        win,
        atoms.net_wm_state,
        atoms.atom,
        &[atoms.net_wm_state_above.resource_id()],
    )?;
    change_property_32(conn, win, atoms.net_wm_desktop, atoms.cardinal, &[u32::MAX])?;
    update_strut(conn, atoms, win, 0, 0, width, bar_height)?;
    change_property_8(conn, win, atoms.net_wm_name, atoms.utf8_string, b"xcb_bar")
}

// ---------------- Platform integration ----------------
struct WindowAdapter<'a> {
    conn: &'a xcb::Connection,
    screen: &'a x::Screen,
    atoms: &'a Atoms,
    win: x::Window,
    bar_height: Cell<u16>,
    process_actions: RefCell<ProcessActionHandler>,
}

impl WindowAdapter<'_> {
    fn sync_bar_height(&self, bar: &mut CairoBar, height: u16) {
        // A window manager may enforce its configured dock height instead of
        // the size requested when the window was created. Keep both future
        // geometry requests and the presentation viewport fill in sync with
        // that final server-side height.
        self.bar_height.set(height);
        bar.config_mut().bar_height = f32::from(height);
    }

    fn apply_runtime_update(&self, update: RuntimeUpdate) -> Result<bool> {
        let needs_redraw = update.needs_redraw();
        for issue in update.issues {
            warn!("xbar runtime issue: {issue:?}");
        }
        for effect in update.platform_effects {
            self.apply_effect(effect)?;
        }
        Ok(needs_redraw)
    }

    fn apply_effect(&self, effect: BarEffect) -> Result<()> {
        match effect {
            BarEffect::ApplyMonitorGeometry(geometry) => self.apply_geometry(geometry),
            BarEffect::ClearMonitorGeometry => self.apply_geometry(MonitorGeometry {
                x: 0,
                y: 0,
                width: u32::from(self.screen.width_in_pixels()),
                height: u32::from(self.screen.height_in_pixels()),
            }),
            effect @ (BarEffect::Screenshot | BarEffect::OpenAudioControl) => {
                self.process_actions.borrow_mut().handle(effect)?;
                Ok(())
            }
            BarEffect::WindowManager(command) => {
                warn!("no shared transport handled window-manager command: {command:?}");
                Ok(())
            }
            BarEffect::ToggleMute
            | BarEffect::AdjustVolume(_)
            | BarEffect::AdjustBrightness(_)
            | BarEffect::RefreshBattery => {
                warn!("enabled xbar provider unexpectedly returned platform effect: {effect:?}");
                Ok(())
            }
        }
    }

    fn apply_geometry(&self, geometry: MonitorGeometry) -> Result<()> {
        let width = geometry.width.max(1);
        let bar_height = self.bar_height.get();
        self.conn.send_and_check_request(&x::ConfigureWindow {
            window: self.win,
            value_list: &[
                x::ConfigWindow::X(geometry.x),
                x::ConfigWindow::Y(geometry.y),
                x::ConfigWindow::Width(width),
                x::ConfigWindow::Height(u32::from(bar_height)),
            ],
        })?;
        update_strut(
            self.conn, self.atoms, self.win, geometry.x, geometry.y, width, bar_height,
        )?;
        self.conn.flush()?;
        Ok(())
    }
}

fn pointer_action(button: u8) -> Option<PointerAction> {
    match button {
        1 => Some(PointerAction::Primary),
        3 => Some(PointerAction::Secondary),
        4 => Some(PointerAction::ScrollUp),
        5 => Some(PointerAction::ScrollDown),
        _ => None,
    }
}

fn redraw(
    cairo_xcb: &CairoXcb,
    window: &WindowAdapter<'_>,
    back: &mut BackBuffer,
    gc: x::Gcontext,
    width: u16,
    height: u16,
    bar: &mut CairoBar,
) -> Result<()> {
    let context = back.ensure_context(cairo_xcb)?;
    bar.render(context, Size::new(f32::from(width), f32::from(height)))?;
    let _ = bar.runtime_mut().take_changes();
    back.flush();
    back.blit_to_window(window.conn, window.win, gc)?;
    window.conn.flush()?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn handle_x_event(
    event: xcb::Event,
    cairo_xcb: &CairoXcb,
    window: &WindowAdapter<'_>,
    back: &mut BackBuffer,
    gc: x::Gcontext,
    current_width: &mut u16,
    current_height: &mut u16,
    bar: &mut CairoBar,
) -> Result<()> {
    let mut should_redraw = false;

    match event {
        xcb::Event::X(x::Event::Expose(event)) => {
            if event.count() == 0 {
                back.blit_to_window(window.conn, window.win, gc)?;
                window.conn.flush()?;
            }
        }
        xcb::Event::X(x::Event::ConfigureNotify(event)) if event.window() == window.win => {
            *current_width = event.width();
            *current_height = event.height();
            window.sync_bar_height(bar, event.height());
            back.resize_if_needed(window.conn, window.win, *current_width, *current_height)?;
            should_redraw = true;
        }
        xcb::Event::X(x::Event::EnterNotify(event)) => {
            should_redraw = bar.pointer_motion(Point::new(
                f32::from(event.event_x()),
                f32::from(event.event_y()),
            ));
        }
        xcb::Event::X(x::Event::LeaveNotify(_)) => {
            should_redraw = bar.pointer_leave();
        }
        xcb::Event::X(x::Event::MotionNotify(event)) => {
            should_redraw = bar.pointer_motion(Point::new(
                f32::from(event.event_x()),
                f32::from(event.event_y()),
            ));
        }
        xcb::Event::X(x::Event::ButtonPress(event)) => {
            let button = event.detail();
            if let Some(input) = pointer_action(button) {
                let update = bar.pointer_action(
                    Point::new(f32::from(event.event_x()), f32::from(event.event_y())),
                    input,
                );
                should_redraw = window.apply_runtime_update(update)?;
            }
        }
        _ => {}
    }

    if should_redraw {
        redraw(
            cairo_xcb,
            window,
            back,
            gc,
            *current_width,
            *current_height,
            bar,
        )?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn drain_x_events(
    cairo_xcb: &CairoXcb,
    window: &WindowAdapter<'_>,
    back: &mut BackBuffer,
    gc: x::Gcontext,
    current_width: &mut u16,
    current_height: &mut u16,
    bar: &mut CairoBar,
) -> Result<()> {
    loop {
        match window.conn.poll_for_event() {
            Ok(Some(event)) => handle_x_event(
                event,
                cairo_xcb,
                window,
                back,
                gc,
                current_width,
                current_height,
                bar,
            )?,
            Ok(None) => return Ok(()),
            Err(error) => return Err(error.into()),
        }
    }
}

fn create_epoll() -> io::Result<OwnedFd> {
    let raw_fd = unsafe { libc::epoll_create1(libc::EPOLL_CLOEXEC) };
    if raw_fd < 0 {
        Err(io::Error::last_os_error())
    } else {
        // SAFETY: epoll_create1 returned a new descriptor whose sole owner is
        // transferred into OwnedFd.
        Ok(unsafe { OwnedFd::from_raw_fd(raw_fd) })
    }
}

fn epoll_add(epoll: RawFd, descriptor: RawFd, token: u64) -> io::Result<()> {
    let mut event = libc::epoll_event {
        events: libc::EPOLLIN as u32,
        u64: token,
    };
    let result = unsafe { libc::epoll_ctl(epoll, libc::EPOLL_CTL_ADD, descriptor, &mut event) };
    if result < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

fn epoll_wait(epoll: RawFd, events: &mut [libc::epoll_event]) -> io::Result<usize> {
    loop {
        let ready = unsafe {
            libc::epoll_wait(
                epoll,
                events.as_mut_ptr(),
                i32::try_from(events.len()).unwrap_or(i32::MAX),
                -1,
            )
        };
        if ready >= 0 {
            return Ok(ready as usize);
        }
        let error = io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::EINTR) {
            return Err(error);
        }
    }
}

fn sync_notifier(
    slot: &mut TransportNotifierSlot,
    runtime: &BarRuntime,
    epoll: RawFd,
) -> Result<()> {
    if let NotifierChange::Replaced { fd, .. } = slot.sync(runtime)? {
        epoll_add(epoll, fd.as_raw_fd(), SHARED_TOKEN)?;
    }
    Ok(())
}

fn main() -> Result<()> {
    let shared_path = env::args().skip(1).last().unwrap_or_default();
    xbar_core::logging::init("xcb_bar", &shared_path)?;

    let runtime = if shared_path.is_empty() {
        BarRuntime::new(ModelConfig::default())?
    } else {
        let recovery = TransportRecoveryConfig::new(shared_path.clone(), TRANSPORT_RETRY_INTERVAL)?;
        BarRuntime::with_managed_transport(ModelConfig::default(), recovery)?
    };

    let (conn, screen_num) = xcb::Connection::connect(None)?;
    let setup = conn.get_setup();
    let screen = setup
        .roots()
        .nth(screen_num as usize)
        .ok_or_else(|| anyhow!("no X screen found"))?;
    let cairo_xcb = build_cairo_xcb(&conn, screen)?;

    let presentation = PresentationConfig::default();
    let bar_height = presentation
        .bar_height
        .round()
        .clamp(1.0, f32::from(u16::MAX)) as u16;
    let font_name = env::var("XBAR_FONT").unwrap_or_else(|_| "monospace 11".to_owned());
    let font = FontDescription::from_string(&font_name);
    let mut bar = CairoBar::new(runtime, presentation, font);

    let win = conn.generate_id();
    let gc = conn.generate_id();
    conn.send_and_check_request(&x::CreateGc {
        cid: gc,
        drawable: x::Drawable::Window(screen.root()),
        value_list: &[],
    })?;

    let mut current_width = screen.width_in_pixels();
    let mut current_height = bar_height;
    conn.send_and_check_request(&x::CreateWindow {
        depth: x::COPY_FROM_PARENT as u8,
        wid: win,
        parent: screen.root(),
        x: 0,
        y: 0,
        width: current_width,
        height: current_height,
        border_width: 0,
        class: x::WindowClass::InputOutput,
        visual: screen.root_visual(),
        value_list: &[
            x::Cw::BackPixmap(x::Pixmap::none()),
            x::Cw::EventMask(
                x::EventMask::EXPOSURE
                    | x::EventMask::STRUCTURE_NOTIFY
                    | x::EventMask::BUTTON_PRESS
                    | x::EventMask::POINTER_MOTION
                    | x::EventMask::ENTER_WINDOW
                    | x::EventMask::LEAVE_WINDOW,
            ),
        ],
    })?;

    let atoms = intern_atoms(&conn)?;
    set_dock_properties(&conn, &atoms, win, u32::from(current_width), current_height)?;
    conn.send_and_check_request(&x::MapWindow { window: win })?;
    conn.flush()?;

    let window = WindowAdapter {
        conn: &conn,
        screen,
        atoms: &atoms,
        win,
        bar_height: Cell::new(bar_height),
        process_actions: RefCell::new(ProcessActionHandler::default()),
    };
    let mut back = BackBuffer::new(
        window.conn,
        window.screen,
        window.win,
        current_width,
        current_height,
    )?;

    // Seed providers and consume any snapshot that was queued before startup.
    let mut initial_update = bar.tick();
    initial_update.merge(bar.poll_transport());
    window.apply_runtime_update(initial_update)?;
    redraw(
        &cairo_xcb,
        &window,
        &mut back,
        gc,
        current_width,
        current_height,
        &mut bar,
    )?;

    let timer = AlignedTimer::new(Duration::from_secs(1))?;
    let epoll = create_epoll()?;
    epoll_add(epoll.as_raw_fd(), window.conn.as_raw_fd(), X_TOKEN)?;
    epoll_add(epoll.as_raw_fd(), timer.as_raw_fd(), TIMER_TOKEN)?;
    let mut notifier_slot = TransportNotifierSlot::new(true);
    sync_notifier(&mut notifier_slot, bar.runtime(), epoll.as_raw_fd())?;

    const EVENT_CAPACITY: usize = 32;
    let mut events: [libc::epoll_event; EVENT_CAPACITY] =
        std::array::from_fn(|_| libc::epoll_event { events: 0, u64: 0 });

    loop {
        let ready = epoll_wait(epoll.as_raw_fd(), &mut events)?;
        for event in events.iter().take(ready) {
            match event.u64 {
                X_TOKEN => drain_x_events(
                    &cairo_xcb,
                    &window,
                    &mut back,
                    gc,
                    &mut current_width,
                    &mut current_height,
                    &mut bar,
                )?,
                TIMER_TOKEN => {
                    if timer.drain()? > 0 {
                        let mut update = bar.tick();
                        update.merge(bar.poll_transport());
                        let needs_redraw = window.apply_runtime_update(update)?;
                        sync_notifier(&mut notifier_slot, bar.runtime(), epoll.as_raw_fd())?;
                        if needs_redraw {
                            redraw(
                                &cairo_xcb,
                                &window,
                                &mut back,
                                gc,
                                current_width,
                                current_height,
                                &mut bar,
                            )?;
                        }
                    }
                }
                SHARED_TOKEN => {
                    if let Some(notifier) = notifier_slot.notifier() {
                        notifier.drain()?;
                        let update = bar.poll_transport();
                        let needs_redraw = window.apply_runtime_update(update)?;
                        sync_notifier(&mut notifier_slot, bar.runtime(), epoll.as_raw_fd())?;
                        if needs_redraw {
                            redraw(
                                &cairo_xcb,
                                &window,
                                &mut back,
                                gc,
                                current_width,
                                current_height,
                                &mut bar,
                            )?;
                        }
                    } else {
                        warn!("received shared token without an owned notifier");
                    }
                }
                token => debug!("unexpected epoll token: {token}"),
            }
        }
    }
}
