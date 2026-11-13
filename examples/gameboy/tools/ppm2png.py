import sys, zlib, struct
def read_ppm(path):
    data = open(path, 'rb').read()
    parts = data.split(b'\n', 3)
    assert parts[0] == b'P6'
    w, h = map(int, parts[1].split())
    return w, h, parts[3]
def write_png(path, w, h, rgb, scale=3):
    rows = []
    for y in range(h):
        row = rgb[y*w*3:(y+1)*w*3]
        big = b''.join(row[x*3:x*3+3]*scale for x in range(w))
        rows.extend([b'\x00' + big]*scale)
    raw = b''.join(rows)
    def chunk(t, d): return struct.pack('>I', len(d)) + t + d + struct.pack('>I', zlib.crc32(t+d) & 0xffffffff)
    png = b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', struct.pack('>IIBBBBB', w*scale, h*scale, 8, 2, 0, 0, 0)) + chunk(b'IDAT', zlib.compress(raw, 9)) + chunk(b'IEND', b'')
    open(path, 'wb').write(png)
w, h, rgb = read_ppm(sys.argv[1])
write_png(sys.argv[2], w, h, rgb, int(sys.argv[3]) if len(sys.argv) > 3 else 3)
