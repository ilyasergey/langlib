#!/usr/bin/env python3
"""Render a PPM program as a scaled-up PNG for the documentation.

Brainloller and Piet programs are images, so their spec pages should show
them. Such an image is also *tiny* (Brainloller's `cat.ppm` is three
pixels square), and a browser shown a 3x3 PNG draws a speck. This scales
each codel to a block and, unless `--no-grid` is given, draws a grid
between the blocks, so a reader can count the commands and match them
against the colour table.

With `--no-grid` the output is an exact whole-number enlargement of the
program, so it can be converted back to a PPM and run at `--codel-size
<scale>`; the grid lines of the default are mid grey, which is not a
command colour in either language, and they would fail that round trip.

The grid lines are a presentation device and are not part of the program.
They are drawn in mid grey, which is not one of the ten meaningful
colours.

PNG is written directly: an IHDR, one zlib-compressed IDAT of unfiltered
scanlines, and an IEND. That needs only `zlib` and `struct` from the
standard library, so the docs can be regenerated on a bare checkout with
no image library installed.

Usage:
    python3 scripts/ppm-to-png.py <in.ppm> <out.png> [scale] [--no-grid]
    python3 scripts/ppm-to-png.py --legend <out.png>
"""

import struct
import sys
import zlib

GRID = (128, 128, 128)

# The ten meaningful colours, in the order the spec table lists them.
LEGEND = [
    ((255, 0, 0), ">"),
    ((128, 0, 0), "<"),
    ((0, 255, 0), "+"),
    ((0, 128, 0), "-"),
    ((0, 0, 255), "."),
    ((0, 0, 128), ","),
    ((255, 255, 0), "["),
    ((128, 128, 0), "]"),
    ((0, 255, 255), "rotate cw"),
    ((0, 128, 128), "rotate ccw"),
]


def read_ppm(path):
    """Read an ASCII (P3) PPM into (width, height, [[(r,g,b), ...], ...])."""
    with open(path, "rb") as f:
        data = f.read()
    toks = []
    for line in data.split(b"\n"):
        line = line.split(b"#", 1)[0]
        toks.extend(line.split())
    if not toks or toks[0] != b"P3":
        raise ValueError(f"{path}: not an ASCII PPM (expected magic P3)")
    w, h, maxval = int(toks[1]), int(toks[2]), int(toks[3])
    if maxval != 255:
        raise ValueError(f"{path}: only maxval 255 is supported, got {maxval}")
    vals = [int(t) for t in toks[4:]]
    if len(vals) < w * h * 3:
        raise ValueError(f"{path}: expected {w * h * 3} samples, got {len(vals)}")
    rows = []
    for y in range(h):
        row = []
        for x in range(w):
            i = (y * w + x) * 3
            row.append((vals[i], vals[i + 1], vals[i + 2]))
        rows.append(row)
    return w, h, rows


def write_png(path, width, height, rows):
    """Write truecolour 8-bit PNG from a list of rows of (r, g, b)."""
    raw = bytearray()
    for row in rows:
        raw.append(0)  # filter type 0 (None)
        for r, g, b in row:
            raw += bytes((r, g, b))

    def chunk(tag, payload):
        return (struct.pack(">I", len(payload)) + tag + payload
                + struct.pack(">I", zlib.crc32(tag + payload) & 0xFFFFFFFF))

    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)
    with open(path, "wb") as f:
        f.write(b"\x89PNG\r\n\x1a\n")
        f.write(chunk(b"IHDR", ihdr))
        f.write(chunk(b"IDAT", zlib.compress(bytes(raw), 9)))
        f.write(chunk(b"IEND", b""))


def upscale(w, h, rows, scale, grid):
    """Blow each codel up to a scale x scale block, optionally gridded."""
    gap = 1 if grid else 0
    out_w = w * scale + gap * (w + 1)
    out_h = h * scale + gap * (h + 1)
    out = [[GRID] * out_w for _ in range(out_h)]
    for y in range(h):
        for x in range(w):
            px = rows[y][x]
            y0 = gap + y * (scale + gap)
            x0 = gap + x * (scale + gap)
            for dy in range(scale):
                line = out[y0 + dy]
                for dx in range(scale):
                    line[x0 + dx] = px
    return out_w, out_h, out


def legend(path, swatch=40, gap=6):
    """A strip of the ten meaningful colours, in spec-table order."""
    n = len(LEGEND)
    w = n * swatch + (n + 1) * gap
    h = swatch + 2 * gap
    # Grey rather than white, so the strip does not read as a white box on a
    # dark page background; it also matches the grid in the program images.
    out = [[GRID] * w for _ in range(h)]
    for i, (rgb, _) in enumerate(LEGEND):
        x0 = gap + i * (swatch + gap)
        for dy in range(swatch):
            line = out[gap + dy]
            for dx in range(swatch):
                line[x0 + dx] = rgb
    write_png(path, w, h, out)
    print(f"{path}: {w}x{h} legend, {n} colours")


def main(argv):
    if len(argv) >= 3 and argv[1] == "--legend":
        legend(argv[2])
        return 0
    if len(argv) < 3:
        print(__doc__)
        return 2
    src, dst = argv[1], argv[2]
    scale = int(argv[3]) if len(argv) > 3 and not argv[3].startswith("-") else 24
    grid = "--no-grid" not in argv
    w, h, rows = read_ppm(src)
    ow, oh, out = upscale(w, h, rows, scale, grid)
    write_png(dst, ow, oh, out)
    print(f"{dst}: {w}x{h} codels -> {ow}x{oh} px (scale {scale}, grid {grid})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
