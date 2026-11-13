"""Run the terminal front end in a pseudo-terminal, then decode its output.

usage: pty_run.py EMULATOR ROM SECONDS OUT.png [KEYS]
KEYS is a string of (delay_seconds, bytes) pairs separated by '|', e.g.
"1.0:\\r|0.5:x" (Enter after 1 s, then X).
The cursor-addressed half-block cells are replayed onto a 160x144 canvas,
which is written as a PNG, and the frame rate from the status line printed.
"""
import os, pty, sys, time, select, re, zlib, struct

emulator, rom, seconds, out_png = sys.argv[1:5]
keys = sys.argv[5] if len(sys.argv) > 5 else ""
pid, fd = pty.fork()
if pid == 0:
    os.environ["TERM"] = "xterm-256color"
    os.execv(emulator, [emulator, rom])
# 200 columns x 80 rows.
import fcntl, termios
fcntl.ioctl(fd, termios.TIOCSWINSZ, struct.pack("HHHH", 80, 200, 0, 0))
data = bytearray()
schedule = []
t0 = time.time()
for item in filter(None, keys.split("|")):
    delay, payload = item.split(":", 1)
    schedule.append((float(delay), payload.encode().decode("unicode_escape").encode("latin-1")))
deadline = t0 + float(seconds)
elapsed_keys = 0.0
next_key = 0
while time.time() < deadline:
    if next_key < len(schedule) and time.time() - t0 >= elapsed_keys + schedule[next_key][0]:
        elapsed_keys += schedule[next_key][0]
        os.write(fd, schedule[next_key][1])
        next_key += 1
    r, _, _ = select.select([fd], [], [], 0.02)
    if r:
        try:
            data += os.read(fd, 1 << 16)
        except OSError:
            break
os.write(fd, b"q")
end = time.time() + 3
while time.time() < end:
    r, _, _ = select.select([fd], [], [], 0.05)
    if r:
        try:
            chunk = os.read(fd, 1 << 16)
        except OSError:
            break
        if not chunk:
            break
        data += chunk
_, status = os.waitpid(pid, 0)
print("exit status:", os.waitstatus_to_exitcode(status), "bytes:", len(data))

# Replay: track cursor and colours; each U+2580 paints two pixels.
canvas = [[(0, 0, 0)] * 160 for _ in range(144)]
row = col = 0
fg = bg = (0, 0, 0)
text = data.decode("utf-8", "replace")
i = 0
fps = re.findall(r"\| (\d+) fps", text)
while i < len(text):
    ch = text[i]
    if ch == "\x1b" and i + 1 < len(text) and text[i + 1] == "[":
        m = re.match(r"\x1b\[([0-9;?<>]*)([A-Za-z])", text[i:])
        if not m:
            i += 1
            continue
        params, final = m.group(1), m.group(2)
        if final == "H":
            parts = [int(p) for p in params.split(";") if p.isdigit()]
            row = (parts[0] if parts else 1) - 1
            col = (parts[1] if len(parts) > 1 else 1) - 1
        elif final == "m":
            parts = params.split(";")
            if len(parts) == 5 and parts[1] == "2":
                rgb = tuple(int(p) for p in parts[2:])
                if parts[0] == "38":
                    fg = rgb
                elif parts[0] == "48":
                    bg = rgb
        i += m.end()
        continue
    if ch == "▀":
        if 0 <= row < 72 and 0 <= col < 160:
            canvas[row * 2][col] = fg
            canvas[row * 2 + 1][col] = bg
        col += 1
    elif ch not in "\r\n":
        col += 1
    i += 1
print("fps reports:", fps[-5:])
scale = 3
raw = b"".join(
    b"\x00" + b"".join(bytes(px) * scale for px in line)
    for line in canvas for _ in range(scale)
)
def chunk(t, d):
    return struct.pack(">I", len(d)) + t + d + struct.pack(">I", zlib.crc32(t + d) & 0xFFFFFFFF)
open(out_png, "wb").write(
    b"\x89PNG\r\n\x1a\n"
    + chunk(b"IHDR", struct.pack(">IIBBBBB", 160 * scale, 144 * scale, 8, 2, 0, 0, 0))
    + chunk(b"IDAT", zlib.compress(raw, 9))
    + chunk(b"IEND", b"")
)
