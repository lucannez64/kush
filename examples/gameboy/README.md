# A Game Boy in Kush

An emulator of the original Game Boy (DMG), written in Kush: the Sharp SM83
CPU with every instruction, the memory map, the timer, interrupts, OAM DMA, the
joypad, the serial port, the picture processor with background, window and
sprites, and the MBC1, MBC3 and MBC5 cartridge controllers. It runs headless
for testing and plays in a terminal.

![Blargg's cpu_instrs, passed](images/cpu_instrs.png)

## Results

- **A real game**: Sanqui's open-source [2048-gb](https://github.com/Sanqui/2048-gb)
  (zlib licence; the ROM is in the [Homebrew Hub database](https://github.com/gbdev/database/tree/master/entries/2048gb))
  boots, shows its title screen, and plays in the terminal at a steady
  60 frames per second: arrow keys slide and merge the tiles, and the score
  and the cartridge-RAM high score update.

| Title screen (headless) | Playing, decoded from the terminal output |
| --- | --- |
| ![2048 title](images/2048_title.png) | ![2048 in play](images/2048_terminal.png) |

- **Blargg's `cpu_instrs`**: all 11 parts pass, individually and as the
  combined MBC1 cartridge. **`instr_timing`** passes too, so every
  instruction takes the right number of cycles.
- **Speed**: the combined `cpu_instrs` run (227 million emulated clock cycles)
  takes 0.83 s in an LLVM build, about **65 times the real console's speed**,
  and 5 s in a Cranelift development build (11 times). The LLVM build compiles
  in 2.8 s, a development build in 0.5 s.
- **Graphics**: `tools/make_ppu_test.py` writes a ROM whose scene exercises
  scrolling, the window, 8×16 sprites, X and Y flips, both sprite palettes and
  the behind-background flag; the screenshot matches the hardware rules for
  each. The terminal front end's output, decoded back to pixels, matches the
  headless screenshot exactly.
- **Terminal**: a steady 60 frames per second; after the first frame, only
  changed cells are sent.

![The PPU test scene, as drawn in a terminal](images/ppu_test_terminal.png)

## Build and run

From this directory, with a current `kush`, Cargo and a C linker:

```sh
kush build --release --backend llvm      # or plain `kush build` for a fast build
./target/kush/gameboy game.gb             # play in the terminal
./target/kush/gameboy test.gb 3000        # run 3000 frames headless; print serial output
./target/kush/gameboy test.gb 600 shot.ppm  # ...and save the last frame
kush test                                 # the emulator's own tests
```

Controls: arrows or WASD, X or K for A, Z or J for B, Enter for Start, Space
for Select, Q to quit. The screen needs a terminal at least 160 columns by 73
rows with true colour. Where the terminal supports the kitty keyboard protocol
(kitty, WezTerm, foot, Ghostty, recent iTerm2), key releases are exact;
elsewhere a key counts as held for 180 ms after each press or autorepeat.

Test ROMs are not included. Blargg's are at
`https://github.com/retrio/gb-test-roms`; run, for example,
`./target/kush/gameboy cpu_instrs/cpu_instrs.gb 6000`.

## How it is built

| File | What it holds |
| --- | --- |
| `src/cartridge.kush` | The `Mapper` trait and one implementation per controller: `Plain`, `Mbc1`, `Mbc3`, `Mbc5`. |
| `src/machine.kush` | `Machine<M: Mapper>`: registers, memories, I/O registers; the bus, timer, DMA, joypad and serial port. |
| `src/cpu.kush` | The instruction set, decoded into the `Reg8`, `Pair`, `Alu`, `Cond` and `Shift` enums. |
| `src/ppu.kush` | Scanline timing, STAT interrupts and line rendering. |
| `src/emulator.kush` | The frame loop and screenshots. |
| `src/terminal.kush` | The terminal renderer and frame pacing. |
| `terminal/` | A Rust adapter with no dependencies: raw mode and key events. |
| `tests/main.kush` | DAA, the stack, a timer interrupt waking HALT, MBC1 banking, frame length. |

Some choices that show the language:

- **The machine is generic over its cartridge.** `main` reads the header and
  calls `play` with the right controller; each controller gets its own
  specialized emulator, and the bus calls `m.cartridge.load(address)` with no
  dispatch at run time.
- **Intended wraparound is explicit.** Registers are `u8` and `u16`;
  `Int.wrapping_add(m.pc, 1)` says the program counter wraps, and any other
  overflow would be a bug that Kush stops on.
- **Opcodes decode into enums.** `ld r, r'` is written once over `Reg8`, which
  includes `Hl` for the byte at address HL.
- **Two-phase borrows.** `push(m, m.pc)` and `machine.write(m, hl(m), value)`
  read `m` in an argument while passing `m` exclusively.

## What it needed from the compiler

Writing it this way needed six additions to Kush, made alongside it and
documented in [places](../../docs/places.md): module-level `const`, indexing
and index assignment on `Vec` fields through references, field assignment on
`let mut` records, method calls on fields and through references, two-phase
exclusive borrows in calls, and records without size limits.

## Not yet

- No sound, no Game Boy Color, no serial link, no saved games (cartridge RAM
  lives as long as the process), and the MBC3 clock reads as stopped.
- The HALT bug and the exact timing of reads and writes inside an instruction
  are not modelled: an instruction's memory accesses happen at its start, and
  the picture processor draws each line whole when it finishes.
- Not checked against `dmg-acid2` yet: no built ROM could be fetched in the
  environment this was written in; it builds from source with RGBDS.
