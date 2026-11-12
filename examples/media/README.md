# media: a window, input, gamepads and sound for Kush

A Kush package that opens a window showing an RGB image, reports keyboard and
gamepad events as typed Kush values, and plays an audio stream. It sits on the
system's SDL2, which is linked, not bundled: install it with your package
manager (`libsdl2-dev`, `media-libs/libsdl2`, `sdl2`, ...).

```toml
[dependencies]
media = { path = "../media" }
```

```kush
use media.window;
use media.input.Event;
use media.input.Key;
use media.audio;

let win = window.open(&Bytes.from("Demo"), 160, 144, 4)?;  // 160x144, shown 4x
let sound = audio.open(48000, 2)?;                         // stereo, 48 kHz
loop {
    match window.next_event(&win) {
        Option.Some(Event.KeyDown(Key.Escape)) => { break; },
        Option.Some(Event.ButtonDown(pad, button)) => { /* a gamepad */ },
        Option.Some(_) => {},
        Option.None => {
            let _ = window.present(&win, &pixels);   // 160 * 144 * 3 RGB bytes
            let _ = audio.queue(&sound, &samples);   // signed 16-bit, interleaved
        },
    }
}
audio.close(sound);
window.close(win);
```

`Window` and `Audio` are linear: the checker rejects a program in which some
path forgets to `close` one, closes it twice, or uses it after closing it, so
a window or device is never leaked or used once released.

## API

| Module | What it has |
| --- | --- |
| `media.window` | `Window` (linear), `open`, `close`, `present`, `set_title`, `next_event` |
| `media.input` | `Event` (`Quit`, `KeyDown`/`KeyUp`, `ButtonDown`/`ButtonUp`, `AxisMoved`, `PadAdded`/`PadRemoved`), `Key`, `Button`, `Axis` |
| `media.audio` | `Audio` (linear), `open`, `close`, `queue`, `queued`, `push` (encode one sample) |

- **Window**: the image is scaled with sharp pixels and keeps its aspect ratio
  when the window is resized. `open` fails with `ENODEV` (19) when there is no
  display, so a program can fall back to something else.
- **Keys** are reported by meaning (`Key.Up`, `Key.Char(120)` for `x`,
  `Key.Function(5)`); key auto-repeat is filtered out.
- **Gamepads** use SDL's controller database, so any common pad reports the
  same standard buttons (`South`, `East`, ..., `DpadLeft`, `Start`) and axes
  (sticks -32768..32767, triggers 0..32767). Pads are opened as they are
  connected, including those present at start; each event carries the pad's
  id.
- **Audio** is a queue: the program pushes samples and the device plays them in
  order. `queued` tells how far ahead the program is, which is also a clock to
  pace a game loop by.

## How it is built

`src/*.kush` is the typed API. `native/` is a Rust adapter with no
dependencies: it declares the ~30 SDL2 functions it uses by hand and exports
C-ABI functions in Kush's bridge ABI (`docs/native-interop.md`). Events cross
that boundary packed into one integer each and are decoded by `media.input`, so
programs only see the enums.

## Tests

- `kush test` (Kush): key, gamepad and axis decoding, sample encoding.
- `cargo test -- --test-threads=1` in `native/`: a **virtual SDL gamepad** is
  connected, its buttons, d-pad and stick moved, and disconnected, through
  SDL's real controller pipeline; the audio queue accepts and accounts for
  samples.
- The Game Boy example runs it for real on a virtual X display: screenshots
  read back from the display server, key presses sent with `xdotool`, and the
  audio stream captured by SDL's disk driver (see its README).
