//! Native side of the Kush `media` package: a window with keyboard and
//! gamepad input, and an audio output stream, on the system's SDL2.
//!
//! Every exported function follows Kush's bridge ABI v1
//! (docs/native-interop.md): scalars, `&Bytes` as pointer and length,
//! opaque resources as one-word handles, and `Result<T, i64>` as a status
//! code with an out slot. Events cross as one packed `i64` each, decoded
//! into typed Kush enums by `media.input`.

use std::ffi::{CStr, c_char, c_int, c_void};
use std::ptr;

#[allow(non_camel_case_types)]
type SDL_Window = c_void;
#[allow(non_camel_case_types)]
type SDL_Renderer = c_void;
#[allow(non_camel_case_types)]
type SDL_Texture = c_void;
#[allow(non_camel_case_types)]
type SDL_GameController = c_void;
#[allow(non_camel_case_types)]
type SDL_Joystick = c_void;

/// `SDL_Event` is a 56-byte union; fields are read at their documented
/// offsets.
#[repr(C, align(8))]
struct Event([u8; 56]);

#[repr(C)]
struct AudioSpec {
    freq: c_int,
    format: u16,
    channels: u8,
    silence: u8,
    samples: u16,
    padding: u16,
    size: u32,
    callback: *const c_void,
    userdata: *mut c_void,
}

unsafe extern "C" {
    fn SDL_InitSubSystem(flags: u32) -> c_int;
    fn SDL_GetError() -> *const c_char;
    fn SDL_SetHint(name: *const c_char, value: *const c_char) -> c_int;
    fn SDL_CreateWindow(title: *const c_char, x: c_int, y: c_int, w: c_int, h: c_int, flags: u32) -> *mut SDL_Window;
    fn SDL_DestroyWindow(window: *mut SDL_Window);
    fn SDL_SetWindowTitle(window: *mut SDL_Window, title: *const c_char);
    fn SDL_CreateRenderer(window: *mut SDL_Window, index: c_int, flags: u32) -> *mut SDL_Renderer;
    fn SDL_DestroyRenderer(renderer: *mut SDL_Renderer);
    fn SDL_RenderSetLogicalSize(renderer: *mut SDL_Renderer, w: c_int, h: c_int) -> c_int;
    fn SDL_CreateTexture(renderer: *mut SDL_Renderer, format: u32, access: c_int, w: c_int, h: c_int) -> *mut SDL_Texture;
    fn SDL_DestroyTexture(texture: *mut SDL_Texture);
    fn SDL_UpdateTexture(texture: *mut SDL_Texture, rect: *const c_void, pixels: *const c_void, pitch: c_int) -> c_int;
    fn SDL_RenderClear(renderer: *mut SDL_Renderer) -> c_int;
    fn SDL_RenderCopy(renderer: *mut SDL_Renderer, texture: *mut SDL_Texture, src: *const c_void, dst: *const c_void) -> c_int;
    fn SDL_RenderPresent(renderer: *mut SDL_Renderer);
    fn SDL_PollEvent(event: *mut Event) -> c_int;
    fn SDL_IsGameController(index: c_int) -> u32;
    fn SDL_GameControllerOpen(index: c_int) -> *mut SDL_GameController;
    fn SDL_GameControllerClose(controller: *mut SDL_GameController);
    fn SDL_GameControllerGetJoystick(controller: *mut SDL_GameController) -> *mut SDL_Joystick;
    fn SDL_JoystickInstanceID(joystick: *mut SDL_Joystick) -> i32;
    fn SDL_OpenAudioDevice(device: *const c_char, capture: c_int, desired: *const AudioSpec, obtained: *mut AudioSpec, changes: c_int) -> u32;
    fn SDL_CloseAudioDevice(device: u32);
    fn SDL_PauseAudioDevice(device: u32, pause: c_int);
    fn SDL_QueueAudio(device: u32, data: *const c_void, len: u32) -> c_int;
    fn SDL_GetQueuedAudioSize(device: u32) -> u32;
}

const INIT_AUDIO: u32 = 0x10;
const INIT_VIDEO: u32 = 0x20;
const INIT_GAMECONTROLLER: u32 = 0x2000;
const WINDOWPOS_CENTERED: c_int = 0x2FFF0000;
const WINDOW_SHOWN: u32 = 0x4;
const WINDOW_RESIZABLE: u32 = 0x20;
const RENDERER_ACCELERATED: u32 = 0x2;
const PIXELFORMAT_RGB24: u32 = 0x17101803;
const TEXTUREACCESS_STREAMING: c_int = 1;
const AUDIO_S16LSB: u16 = 0x8010;

// SDL event types.
const QUIT: u32 = 0x100;
const KEYDOWN: u32 = 0x300;
const KEYUP: u32 = 0x301;
const CONTROLLERAXISMOTION: u32 = 0x650;
const CONTROLLERBUTTONDOWN: u32 = 0x651;
const CONTROLLERBUTTONUP: u32 = 0x652;
const CONTROLLERDEVICEADDED: u32 = 0x653;
const CONTROLLERDEVICEREMOVED: u32 = 0x654;

// Event kinds as `media.input` decodes them.
pub const KIND_QUIT: u64 = 1;
pub const KIND_KEY_DOWN: u64 = 2;
pub const KIND_KEY_UP: u64 = 3;
pub const KIND_BUTTON_DOWN: u64 = 4;
pub const KIND_BUTTON_UP: u64 = 5;
pub const KIND_AXIS: u64 = 6;
pub const KIND_PAD_ADDED: u64 = 7;
pub const KIND_PAD_REMOVED: u64 = 8;

// Error codes returned to Kush (positive errno-like values).
const ENODEV: i64 = 19;
const EINVAL: i64 = 22;
const EIO: i64 = 5;

/// One event as an `i64`: kind in bits 0-7, device in 8-15, code in 16-47,
/// a signed 16-bit value in 48-63. Zero means no event.
pub fn pack(kind: u64, device: i64, code: i64, value: i64) -> i64 {
    (kind | ((device as u64 & 0xFF) << 8) | ((code as u64 & 0xFFFF_FFFF) << 16) | ((value as u64 & 0xFFFF) << 48)) as i64
}

fn error_text() -> String {
    unsafe {
        let text = SDL_GetError();
        if text.is_null() { String::new() } else { CStr::from_ptr(text).to_string_lossy().into_owned() }
    }
}

fn c_string(pointer: *const u8, length: i64) -> Vec<u8> {
    let mut text = if pointer.is_null() || length <= 0 {
        Vec::new()
    } else {
        unsafe { std::slice::from_raw_parts(pointer, length as usize) }.to_vec()
    };
    text.retain(|&byte| byte != 0);
    text.push(0);
    text
}

struct Window {
    window: *mut SDL_Window,
    renderer: *mut SDL_Renderer,
    texture: *mut SDL_Texture,
    width: i64,
    height: i64,
    controllers: Vec<(i32, *mut SDL_GameController)>,
}

/// Open a window showing a `width` x `height` image scaled by `scale`,
/// with nearest-neighbour scaling and the aspect ratio kept on resize.
#[unsafe(no_mangle)]
pub extern "C" fn media_window_open(title: *const u8, title_length: i64, width: i64, height: i64, scale: i64, out: *mut i64) -> i64 {
    if width <= 0 || height <= 0 || scale <= 0 || width > 16384 || height > 16384 || out.is_null() {
        return EINVAL;
    }
    unsafe {
        if SDL_InitSubSystem(INIT_VIDEO | INIT_GAMECONTROLLER) != 0 {
            eprintln!("media: {}", error_text());
            return ENODEV;
        }
        SDL_SetHint(c"SDL_RENDER_SCALE_QUALITY".as_ptr(), c"0".as_ptr());
        let title = c_string(title, title_length);
        let window = SDL_CreateWindow(
            title.as_ptr() as *const c_char,
            WINDOWPOS_CENTERED,
            WINDOWPOS_CENTERED,
            (width * scale) as c_int,
            (height * scale) as c_int,
            WINDOW_SHOWN | WINDOW_RESIZABLE,
        );
        if window.is_null() {
            eprintln!("media: {}", error_text());
            return ENODEV;
        }
        let mut renderer = SDL_CreateRenderer(window, -1, RENDERER_ACCELERATED);
        if renderer.is_null() {
            renderer = SDL_CreateRenderer(window, -1, 0);
        }
        if renderer.is_null() {
            eprintln!("media: {}", error_text());
            SDL_DestroyWindow(window);
            return ENODEV;
        }
        SDL_RenderSetLogicalSize(renderer, width as c_int, height as c_int);
        let texture = SDL_CreateTexture(renderer, PIXELFORMAT_RGB24, TEXTUREACCESS_STREAMING, width as c_int, height as c_int);
        if texture.is_null() {
            eprintln!("media: {}", error_text());
            SDL_DestroyRenderer(renderer);
            SDL_DestroyWindow(window);
            return ENODEV;
        }
        let state = Box::new(Window { window, renderer, texture, width, height, controllers: Vec::new() });
        *out = Box::into_raw(state) as i64;
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn media_window_release(handle: i64) {
    if handle == 0 {
        return;
    }
    let state = unsafe { Box::from_raw(handle as *mut Window) };
    unsafe {
        for (_, controller) in &state.controllers {
            SDL_GameControllerClose(*controller);
        }
        SDL_DestroyTexture(state.texture);
        SDL_DestroyRenderer(state.renderer);
        SDL_DestroyWindow(state.window);
    }
}

fn window<'a>(handle: i64) -> Option<&'a mut Window> {
    if handle == 0 { None } else { Some(unsafe { &mut *(handle as *mut Window) }) }
}

/// Show an RGB image (3 bytes per pixel, rows top to bottom) of the size
/// the window was opened with.
#[unsafe(no_mangle)]
pub extern "C" fn media_window_present(handle: i64, pixels: *const u8, length: i64) -> i64 {
    let Some(state) = window(handle) else { return EINVAL };
    if pixels.is_null() || length != state.width * state.height * 3 {
        return EINVAL;
    }
    unsafe {
        if SDL_UpdateTexture(state.texture, ptr::null(), pixels as *const c_void, (state.width * 3) as c_int) != 0 {
            return EIO;
        }
        SDL_RenderClear(state.renderer);
        SDL_RenderCopy(state.renderer, state.texture, ptr::null(), ptr::null());
        SDL_RenderPresent(state.renderer);
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn media_window_set_title(handle: i64, title: *const u8, length: i64) -> i64 {
    let Some(state) = window(handle) else { return EINVAL };
    let title = c_string(title, length);
    unsafe { SDL_SetWindowTitle(state.window, title.as_ptr() as *const c_char) };
    0
}

fn u32_at(event: &Event, offset: usize) -> u32 {
    u32::from_ne_bytes(event.0[offset..offset + 4].try_into().unwrap())
}
fn i32_at(event: &Event, offset: usize) -> i32 {
    i32::from_ne_bytes(event.0[offset..offset + 4].try_into().unwrap())
}
fn i16_at(event: &Event, offset: usize) -> i16 {
    i16::from_ne_bytes(event.0[offset..offset + 2].try_into().unwrap())
}

/// Translate one SDL event; `None` for events Kush does not see.
fn translate(state: &mut Window, event: &Event) -> Option<i64> {
    let kind = u32_at(event, 0);
    match kind {
        QUIT => Some(pack(KIND_QUIT, 0, 0, 0)),
        KEYDOWN | KEYUP => {
            // SDL_KeyboardEvent: repeat at 13, keysym.sym at 20.
            if kind == KEYDOWN && event.0[13] != 0 {
                return None;
            }
            let sym = i32_at(event, 20) as i64;
            Some(pack(if kind == KEYDOWN { KIND_KEY_DOWN } else { KIND_KEY_UP }, 0, sym, 0))
        }
        CONTROLLERBUTTONDOWN | CONTROLLERBUTTONUP => {
            // which at 8, button at 12.
            let which = i32_at(event, 8) as i64;
            let button = event.0[12] as i64;
            Some(pack(if kind == CONTROLLERBUTTONDOWN { KIND_BUTTON_DOWN } else { KIND_BUTTON_UP }, which, button, 0))
        }
        CONTROLLERAXISMOTION => {
            // which at 8, axis at 12, value at 16.
            let which = i32_at(event, 8) as i64;
            Some(pack(KIND_AXIS, which, event.0[12] as i64, i16_at(event, 16) as i64))
        }
        CONTROLLERDEVICEADDED => {
            // which is the device index here; the pad is opened and named
            // by its instance id, which later events carry.
            let index = i32_at(event, 8);
            unsafe {
                if SDL_IsGameController(index) == 0 {
                    return None;
                }
                let controller = SDL_GameControllerOpen(index);
                if controller.is_null() {
                    return None;
                }
                let id = SDL_JoystickInstanceID(SDL_GameControllerGetJoystick(controller));
                if state.controllers.iter().any(|(known, _)| *known == id) {
                    SDL_GameControllerClose(controller);
                    return None;
                }
                state.controllers.push((id, controller));
                Some(pack(KIND_PAD_ADDED, id as i64, 0, 0))
            }
        }
        CONTROLLERDEVICEREMOVED => {
            let id = i32_at(event, 8);
            if let Some(at) = state.controllers.iter().position(|(known, _)| *known == id) {
                let (_, controller) = state.controllers.remove(at);
                unsafe { SDL_GameControllerClose(controller) };
            }
            Some(pack(KIND_PAD_REMOVED, id as i64, 0, 0))
        }
        _ => None,
    }
}

/// The next pending event, packed, or 0 when there is none.
#[unsafe(no_mangle)]
pub extern "C" fn media_window_next_event(handle: i64) -> i64 {
    let Some(state) = window(handle) else { return 0 };
    let mut event = Event([0; 56]);
    while unsafe { SDL_PollEvent(&mut event) } != 0 {
        if let Some(packed) = translate(state, &event) {
            return packed;
        }
    }
    0
}

/// Open the default output device for signed 16-bit samples at `rate` Hz
/// with `channels` interleaved channels. The handle is the SDL device id.
#[unsafe(no_mangle)]
pub extern "C" fn media_audio_open(rate: i64, channels: i64, out: *mut i64) -> i64 {
    if !(8000..=192000).contains(&rate) || !(1..=2).contains(&channels) || out.is_null() {
        return EINVAL;
    }
    unsafe {
        if SDL_InitSubSystem(INIT_AUDIO) != 0 {
            eprintln!("media: {}", error_text());
            return ENODEV;
        }
        let desired = AudioSpec {
            freq: rate as c_int,
            format: AUDIO_S16LSB,
            channels: channels as u8,
            silence: 0,
            samples: 1024,
            padding: 0,
            size: 0,
            callback: ptr::null(),
            userdata: ptr::null_mut(),
        };
        let device = SDL_OpenAudioDevice(ptr::null(), 0, &desired, ptr::null_mut(), 0);
        if device == 0 {
            eprintln!("media: {}", error_text());
            return ENODEV;
        }
        SDL_PauseAudioDevice(device, 0);
        *out = device as i64;
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn media_audio_release(handle: i64) {
    if handle != 0 {
        unsafe { SDL_CloseAudioDevice(handle as u32) };
    }
}

/// Queue little-endian signed 16-bit interleaved samples for playback.
#[unsafe(no_mangle)]
pub extern "C" fn media_audio_queue(handle: i64, samples: *const u8, length: i64) -> i64 {
    if handle == 0 || length < 0 || (length > 0 && samples.is_null()) || length > u32::MAX as i64 {
        return EINVAL;
    }
    if length == 0 {
        return 0;
    }
    if unsafe { SDL_QueueAudio(handle as u32, samples as *const c_void, length as u32) } != 0 {
        return EIO;
    }
    0
}

/// Bytes queued and not yet played.
#[unsafe(no_mangle)]
pub extern "C" fn media_audio_queued(handle: i64) -> i64 {
    if handle == 0 { 0 } else { unsafe { SDL_GetQueuedAudioSize(handle as u32) as i64 } }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[link(name = "SDL2")]
    unsafe extern "C" {
        fn SDL_JoystickAttachVirtual(kind: c_int, axes: c_int, buttons: c_int, hats: c_int) -> c_int;
        fn SDL_JoystickDetachVirtual(index: c_int) -> c_int;
        fn SDL_JoystickOpen(index: c_int) -> *mut SDL_Joystick;
        fn SDL_JoystickSetVirtualButton(joystick: *mut SDL_Joystick, button: c_int, value: u8) -> c_int;
        fn SDL_JoystickSetVirtualAxis(joystick: *mut SDL_Joystick, axis: c_int, value: i16) -> c_int;
    }

    /// Wait for the next event of `kind`, polling as a frame loop would.
    fn wait_for(handle: i64, kind: u64) -> Option<i64> {
        for _ in 0..200 {
            let event = media_window_next_event(handle);
            if event != 0 && (event as u64 & 0xFF) == kind {
                return Some(event);
            }
            if event == 0 {
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
        }
        None
    }

    /// A virtual gamepad goes through SDL's real controller pipeline: it is
    /// opened when connected, and its buttons, d-pad and sticks arrive as
    /// packed events with the pad's id.
    #[test]
    fn a_connected_gamepad_reports_buttons_and_sticks() {
        unsafe { std::env::set_var("SDL_VIDEODRIVER", "dummy") };
        let mut handle = 0;
        assert_eq!(media_window_open(b"test".as_ptr(), 4, 160, 144, 1, &mut handle), 0);
        // SDL_JOYSTICK_TYPE_GAMECONTROLLER: 6 axes, 15 buttons, no hats.
        let index = unsafe { SDL_JoystickAttachVirtual(1, 6, 15, 0) };
        assert!(index >= 0, "{}", error_text());
        let added = wait_for(handle, KIND_PAD_ADDED).expect("pad added");
        let pad = (added >> 8) & 0xFF;
        let joystick = unsafe { SDL_JoystickOpen(index) };
        assert!(!joystick.is_null());
        // Button 1 is East; button 14 the d-pad's right.
        unsafe { SDL_JoystickSetVirtualButton(joystick, 1, 1) };
        let down = wait_for(handle, KIND_BUTTON_DOWN).expect("button down");
        assert_eq!(((down >> 8) & 0xFF, (down >> 16) & 0xFFFF_FFFF), (pad, 1));
        unsafe { SDL_JoystickSetVirtualButton(joystick, 1, 0) };
        let up = wait_for(handle, KIND_BUTTON_UP).expect("button up");
        assert_eq!((up >> 16) & 0xFFFF_FFFF, 1);
        unsafe { SDL_JoystickSetVirtualButton(joystick, 14, 1) };
        let right = wait_for(handle, KIND_BUTTON_DOWN).expect("d-pad right");
        assert_eq!((right >> 16) & 0xFFFF_FFFF, 14);
        // Left stick, Y axis, fully up.
        unsafe { SDL_JoystickSetVirtualAxis(joystick, 1, -32768) };
        let axis = wait_for(handle, KIND_AXIS).expect("axis");
        assert_eq!((axis >> 16) & 0xFFFF_FFFF, 1);
        assert_eq!(((axis >> 48) & 0xFFFF) as u16 as i16, -32768);
        unsafe { SDL_JoystickDetachVirtual(index) };
        let removed = wait_for(handle, KIND_PAD_REMOVED).expect("pad removed");
        assert_eq!((removed >> 8) & 0xFF, pad);
        media_window_release(handle);
    }

    /// The audio stream accepts and accounts for queued samples.
    #[test]
    fn audio_queues_samples() {
        unsafe { std::env::set_var("SDL_AUDIODRIVER", "dummy") };
        let mut handle = 0;
        assert_eq!(media_audio_open(48000, 2, &mut handle), 0, "{}", error_text());
        let silence = vec![0u8; 4800];
        assert_eq!(media_audio_queue(handle, silence.as_ptr(), silence.len() as i64), 0);
        assert!(media_audio_queued(handle) <= 4800);
        assert_eq!(media_audio_queue(handle, silence.as_ptr(), -1), EINVAL);
        media_audio_release(handle);
    }

    #[test]
    fn packing_keeps_every_field() {
        let packed = pack(KIND_AXIS, 3, 1, -32768);
        assert_eq!(packed & 0xFF, KIND_AXIS as i64);
        assert_eq!((packed >> 8) & 0xFF, 3);
        assert_eq!((packed >> 16) & 0xFFFF_FFFF, 1);
        assert_eq!(((packed >> 48) & 0xFFFF) as u16 as i16, -32768);
        // SDL keycodes for arrows have bit 30 set; they survive.
        let arrow = pack(KIND_KEY_DOWN, 0, 0x4000_0052, 0);
        assert_eq!((arrow >> 16) & 0xFFFF_FFFF, 0x4000_0052);
    }
}
