"""Write a 32 KiB Game Boy ROM that draws a fixed scene exercising the PPU.

The program is plain machine code, written as immediate stores
(LD A,n / LD (nn),A) so no assembler is needed. Scene:
  - background: tile 1 (light) everywhere, a column of tile 2 (checker)
    every 4th tile column, scrolled right by SCX = 4
  - window: tile 4 (dark solid) from WX = 87, WY = 96 (bottom-right block)
  - sprites (8x8, tile 3 = a right triangle in colour 3):
      0 at (16, 16) normal         1 at (32, 16) X-flipped
      2 at (48, 16) Y-flipped      3 at (64, 16) palette OBP1
      4 at (80, 16) behind non-zero background (only shows on colour-0 BG)
  - second frame: 8x16 sprites (tiles 6,7), so sprite 5 at (100, 40) shows a
    16-pixel-tall shape when LCDC bit 2 is set.
"""
import sys

rom = bytearray(0x8000)
code = bytearray()

def ld_a(n): code.extend([0x3E, n & 0xFF])
def st(addr): code.extend([0xEA, addr & 0xFF, addr >> 8])
def poke(addr, value):
    ld_a(value)
    st(addr)

# Turn the display off (safe: our emulator allows it any time).
poke(0xFF40, 0x00)

def tile(index, rows):
    """rows: 8 lists of 8 colour indices 0-3."""
    base = 0x8000 + index * 16
    for r, row in enumerate(rows):
        low = high = 0
        for c, colour in enumerate(row):
            low |= (colour & 1) << (7 - c)
            high |= ((colour >> 1) & 1) << (7 - c)
        poke(base + r * 2, low)
        poke(base + r * 2 + 1, high)

blank = [[0] * 8 for _ in range(8)]
light = [[1] * 8 for _ in range(8)]
checker = [[2 if (r + c) % 2 == 0 else 3 for c in range(8)] for r in range(8)]
triangle = [[3 if c <= r else 0 for c in range(8)] for r in range(8)]
dark = [[3] * 8 for _ in range(8)]
top_half = [[3 if c < 4 else 0 for c in range(8)] for r in range(8)]
bottom_half = [[2 if c >= 4 else 0 for c in range(8)] for r in range(8)]
tile(0, blank)
tile(1, light)
tile(2, checker)
tile(3, triangle)
tile(4, dark)
tile(6, top_half)
tile(7, bottom_half)

# Background map 0x9800: tile 1, with tile 2 in every 4th column; tile 0 in
# row 2 columns 9-11, so sprite 4 (behind BG) shows only there.
for row in range(18):
    for col in range(21):
        entry = 2 if col % 4 == 0 else 1
        if row == 2 and 9 <= col <= 11:
            entry = 0
        poke(0x9800 + row * 32 + col, entry)
# Window map 0x9C00: all tile 4.
for row in range(6):
    for col in range(10):
        poke(0x9C00 + row * 32 + col, 4)

# OAM: y+16, x+8, tile, attributes.
sprites = [
    (16, 16, 3, 0x00),
    (16, 32, 3, 0x20),
    (16, 48, 3, 0x40),
    (16, 64, 3, 0x10),
    (16, 80, 3, 0x80),
    (40, 100, 6, 0x00),
]
for i, (y, x, t, a) in enumerate(sprites):
    poke(0xFE00 + i * 4, y + 16)
    poke(0xFE00 + i * 4 + 1, x + 8)
    poke(0xFE00 + i * 4 + 2, t)
    poke(0xFE00 + i * 4 + 3, a)
for i in range(len(sprites), 40):
    poke(0xFE00 + i * 4, 0)  # off screen

poke(0xFF47, 0xE4)   # BGP: 0,1,2,3
poke(0xFF48, 0xE4)   # OBP0
poke(0xFF49, 0x1B)   # OBP1: reversed
poke(0xFF43, 4)      # SCX
poke(0xFF42, 0)      # SCY
poke(0xFF4A, 96)     # WY
poke(0xFF4B, 87)     # WX
# LCD on, window map 0x9C00, window on, unsigned tiles, BG map 0x9800,
# 8x16 sprites, sprites on, BG on.
poke(0xFF40, 0x80 | 0x40 | 0x20 | 0x10 | 0x04 | 0x02 | 0x01)
# Loop forever: JR -2.
code.extend([0x18, 0xFE])

start = 0x150
rom[0x100:0x104] = bytes([0x00, 0xC3, start & 0xFF, start >> 8])  # NOP; JP start
rom[0x134:0x13C] = b"PPUTEST"
rom[0x147] = 0x00
rom[start:start + len(code)] = code
assert start + len(code) < 0x8000, len(code)
open(sys.argv[1], "wb").write(rom)
print("code bytes:", len(code))
