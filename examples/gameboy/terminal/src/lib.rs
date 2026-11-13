//! Keyboard input for the Kush Game Boy's terminal front end.
//!
//! Three C-ABI functions, following Kush's bridge ABI v1 (see
//! docs/native-interop.md): enter and leave raw mode, and report which Game
//! Boy buttons are held. Drawing is done by the Kush program itself.
//!
//! Terminals normally send key presses only. Where the terminal supports the
//! kitty keyboard protocol (kitty, WezTerm, foot, Ghostty, recent iTerm2...)
//! it is switched on so that releases are reported too; elsewhere a key counts
//! as held for a short while after each press or autorepeat.

use std::io::Write;
use std::sync::Mutex;
use std::time::{Duration, Instant};

#[repr(C)]
#[derive(Clone, Copy)]
struct Termios {
    iflag: u32,
    oflag: u32,
    cflag: u32,
    lflag: u32,
    line: u8,
    cc: [u8; 32],
    ispeed: u32,
    ospeed: u32,
}

unsafe extern "C" {
    fn tcgetattr(fd: i32, termios: *mut Termios) -> i32;
    fn tcsetattr(fd: i32, when: i32, termios: *const Termios) -> i32;
    fn read(fd: i32, buffer: *mut u8, count: usize) -> isize;
}

const STDIN: i32 = 0;
const TCSANOW: i32 = 0;
const ISIG: u32 = 0o1;
const ICANON: u32 = 0o2;
const ECHO: u32 = 0o10;
const IEXTEN: u32 = 0o100000;
const ICRNL: u32 = 0o400;
const IXON: u32 = 0o2000;
const VTIME: usize = 5;
const VMIN: usize = 6;

// Button bits, as the Kush side reads them.
const RIGHT: i64 = 1 << 0;
const LEFT: i64 = 1 << 1;
const UP: i64 = 1 << 2;
const DOWN: i64 = 1 << 3;
const A: i64 = 1 << 4;
const B: i64 = 1 << 5;
const SELECT: i64 = 1 << 6;
const START: i64 = 1 << 7;
const QUIT: i64 = 1 << 8;

/// Without release events, a key is held this long after its last press.
const LEGACY_HOLD: Duration = Duration::from_millis(180);

struct State {
    saved: Option<Termios>,
    /// Buttons held according to press/release events (kitty protocol).
    down: i64,
    /// Press times for terminals that report presses only.
    pressed_at: [Option<Instant>; 8],
    quit: bool,
    pending: Vec<u8>,
}

static STATE: Mutex<State> = Mutex::new(State {
    saved: None,
    down: 0,
    pressed_at: [None; 8],
    quit: false,
    pending: Vec::new(),
});

fn out(text: &str) {
    let mut stdout = std::io::stdout();
    let _ = stdout.write_all(text.as_bytes());
    let _ = stdout.flush();
}

/// Raw, non-blocking input on an alternate screen with a hidden cursor.
#[unsafe(no_mangle)]
pub extern "C" fn gb_terminal_enter() -> i64 {
    let mut state = STATE.lock().unwrap();
    let mut termios = std::mem::MaybeUninit::<Termios>::uninit();
    if unsafe { tcgetattr(STDIN, termios.as_mut_ptr()) } != 0 {
        return 25; // ENOTTY: not a terminal
    }
    let saved = unsafe { termios.assume_init() };
    let mut raw = saved;
    raw.lflag &= !(ICANON | ECHO | ISIG | IEXTEN);
    raw.iflag &= !(IXON | ICRNL);
    // Reads return at once with whatever is there. (O_NONBLOCK is not
    // used: stdin and stdout share one open file on a terminal, and output
    // must block rather than drop bytes.)
    raw.cc[VMIN] = 0;
    raw.cc[VTIME] = 0;
    if unsafe { tcsetattr(STDIN, TCSANOW, &raw) } != 0 {
        return 25;
    }
    state.saved = Some(saved);
    // Alternate screen, hidden cursor, clear; then ask for the kitty
    // keyboard protocol: disambiguate (1), event types (2), all keys as
    // escape codes (8). Terminals without it ignore the request.
    out("\x1b[?1049h\x1b[?25l\x1b[2J\x1b[>11u");
    0
}

/// Undo `gb_terminal_enter`.
#[unsafe(no_mangle)]
pub extern "C" fn gb_terminal_leave() -> i64 {
    let mut state = STATE.lock().unwrap();
    out("\x1b[<u\x1b[0m\x1b[?25h\x1b[?1049l");
    if let Some(saved) = state.saved.take() {
        unsafe { tcsetattr(STDIN, TCSANOW, &saved) };
    }
    0
}

fn button_for_key(code: u32) -> i64 {
    match code {
        // Arrow keys arrive as letters A-D after CSI and are mapped by the
        // caller; these are the text keys.
        0x77 | 0x57 => UP,    // w
        0x61 | 0x41 => LEFT,  // a
        0x73 | 0x53 => DOWN,  // s
        0x64 | 0x44 => RIGHT, // d
        0x78 | 0x58 | 0x6B | 0x4B => A, // x, k
        0x7A | 0x5A | 0x6A | 0x4A => B, // z, j
        13 | 10 => START,               // Enter
        32 | 127 | 8 => SELECT,         // Space, Backspace
        0x71 | 0x51 | 3 => QUIT,        // q, Ctrl-C
        _ => 0,
    }
}

fn arrow(final_byte: u8) -> i64 {
    match final_byte {
        b'A' => UP,
        b'B' => DOWN,
        b'C' => RIGHT,
        b'D' => LEFT,
        _ => 0,
    }
}

fn press(state: &mut State, button: i64, now: Instant) {
    if button == QUIT {
        state.quit = true;
        return;
    }
    for bit in 0..8 {
        if button & (1 << bit) != 0 {
            state.pressed_at[bit] = Some(now);
        }
    }
}

/// Handle one kitty-protocol event for `button`: 1 press, 2 repeat, 3 release.
fn event(state: &mut State, button: i64, kind: u32) {
    if button == QUIT {
        if kind != 3 {
            state.quit = true;
        }
        return;
    }
    if kind == 3 {
        state.down &= !button;
    } else {
        state.down |= button;
    }
}

/// Parse what is buffered. Returns the number of bytes consumed; an
/// incomplete escape sequence at the end is kept for the next call.
fn parse(state: &mut State, now: Instant) -> usize {
    let bytes = std::mem::take(&mut state.pending);
    let mut at = 0;
    while at < bytes.len() {
        let byte = bytes[at];
        if byte != 0x1b {
            let button = button_for_key(byte as u32);
            press(state, button, now);
            at += 1;
            continue;
        }
        // ESC [ params final  or  ESC O final.
        if at + 1 >= bytes.len() {
            break;
        }
        let introducer = bytes[at + 1];
        if introducer == b'O' {
            if at + 2 >= bytes.len() {
                break;
            }
            press(state, arrow(bytes[at + 2]), now);
            at += 3;
            continue;
        }
        if introducer != b'[' {
            at += 1; // a lone Escape
            continue;
        }
        let mut end = at + 2;
        while end < bytes.len() && !(0x40..=0x7e).contains(&bytes[end]) {
            end += 1;
        }
        if end >= bytes.len() {
            break;
        }
        let final_byte = bytes[end];
        let params = String::from_utf8_lossy(&bytes[at + 2..end]).into_owned();
        at = end + 1;
        // `code;modifiers:event` (kitty) or plain arrows.
        let mut fields = params.split(';');
        let code: u32 = fields.next().and_then(|f| f.split(':').next()?.parse().ok()).unwrap_or(1);
        let second = fields.next();
        let kind: Option<u32> = second.and_then(|f| f.split(':').nth(1)?.parse().ok());
        let control = second
            .and_then(|f| f.split(':').next()?.parse::<u32>().ok())
            .is_some_and(|m| (m.saturating_sub(1)) & 4 != 0);
        let button = match final_byte {
            b'u' if control && code == 0x63 => QUIT, // Ctrl-C
            b'u' => button_for_key(code),
            b'A'..=b'D' => arrow(final_byte),
            _ => continue, // replies to queries and other keys
        };
        if final_byte == b'u' || kind.is_some() {
            event(state, button, kind.unwrap_or(1));
        } else {
            press(state, button, now);
        }
    }
    state.pending = bytes[at..].to_vec();
    at
}

/// The Game Boy buttons held now, as a bitmask (bit 8: quit requested).
#[unsafe(no_mangle)]
pub extern "C" fn gb_terminal_buttons() -> i64 {
    let mut state = STATE.lock().unwrap();
    let mut buffer = [0u8; 256];
    loop {
        let count = unsafe { read(STDIN, buffer.as_mut_ptr(), buffer.len()) };
        if count <= 0 {
            break;
        }
        state.pending.extend_from_slice(&buffer[..count as usize]);
    }
    let now = Instant::now();
    parse(&mut state, now);
    let mut held = state.down;
    for bit in 0..8 {
        if let Some(at) = state.pressed_at[bit] {
            if now.duration_since(at) < LEGACY_HOLD {
                held |= 1 << bit;
            } else {
                state.pressed_at[bit] = None;
            }
        }
    }
    if state.quit {
        held |= QUIT;
    }
    held
}

#[cfg(test)]
mod tests {
    use super::*;

    fn feed(input: &[u8]) -> State {
        let mut state = State {
            saved: None,
            down: 0,
            pressed_at: [None; 8],
            quit: false,
            pending: input.to_vec(),
        };
        parse(&mut state, Instant::now());
        state
    }

    #[test]
    fn kitty_press_and_release() {
        let state = feed(b"\x1b[120u\x1b[1;1:1C");
        assert_eq!(state.down, A | RIGHT);
        let state = feed(b"\x1b[120u\x1b[120;1:3u");
        assert_eq!(state.down, 0);
    }

    #[test]
    fn legacy_keys_and_quit() {
        let state = feed(b"x\x1b[Aq");
        assert!(state.pressed_at[4].is_some());
        assert!(state.pressed_at[2].is_some());
        assert!(state.quit);
    }

    #[test]
    fn incomplete_sequences_wait() {
        let state = feed(b"\x1b[1;1");
        assert_eq!(state.pending, b"\x1b[1;1");
    }
}
