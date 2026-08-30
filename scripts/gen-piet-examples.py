#!/usr/bin/env python3
"""Generate the Piet examples that have loops, branches, or decoration.

    python3 scripts/gen-piet-examples.py

Writes count.ppm, truth.ppm, collatz.ppm and mondrian.ppm into
Langlib/Examples/Piet/, then re-render the pictures with
scripts/render-docs-images.sh.

Nobody paints a Piet program with a loop in it by hand, so this is a tiny
assembler. It knows two layouts, both taken from the codel geometry that
Langlib/Computability/Piet.lean uses and *proves* correct:

* `linear_grid`, after `linearGrid`: three rows, the commands laid left to
  right along the middle one, a white codel and a full-height terminal bar
  at the end that no (DP, CC) attempt can leave.

* `loop_grid`, after `loopGrid`: the commands along the top row, black
  beneath them, and a white return corridor along the bottom. The body ends
  with `pointer`: leave 1 on the stack and the DP turns south into the
  return corridor, leave 0 and it carries straight on east into the
  terminal. That one branch is all the control flow Piet needs.

Everything here is checked by running the programs (`lake test`, suite
"piet"), which is the only honest way to verify a Piet layout.

The generated PPMs are checked in rather than built, because Piet examples
are source files that a reader is expected to look at.
"""

import os
import sys

# --- colours --------------------------------------------------------------

# Codels are (hue, lightness) pairs; hue 0..5 is red, yellow, green, cyan,
# blue, magenta and lightness 0..2 is light, normal, dark.
LIGHT_CHANNELS = {0: (255, 192), 1: (255, 0), 2: (192, 0)}

def rgb(codel):
    if codel == 'W': return (255, 255, 255)
    if codel == 'B': return (0, 0, 0)
    hue, light = codel
    hi, mid = LIGHT_CHANNELS[light]
    return {0: (hi, mid, mid), 1: (hi, hi, mid), 2: (mid, hi, mid),
            3: (mid, hi, hi), 4: (mid, mid, hi), 5: (hi, mid, hi)}[hue]

RED, YELLOW, BLUE = (0, 1), (1, 1), (4, 1)

# A command is a (hue steps, lightness steps) displacement, per the table in
# docs/piet/spec.md.
OPS = {
    'push': (0, 1), 'pop': (0, 2),
    'add': (1, 0), 'sub': (1, 1), 'mul': (1, 2),
    'div': (2, 0), 'mod': (2, 1), 'not': (2, 2),
    'greater': (3, 0), 'pointer': (3, 1), 'switch': (3, 2),
    'dup': (4, 0), 'roll': (4, 1), 'innum': (4, 2),
    'inchar': (5, 0), 'outnum': (5, 1), 'outchar': (5, 2),
}

def advance(codel, name):
    dh, dl = OPS[name]
    return ((codel[0] + dh) % 6, (codel[1] + dl) % 3)

# --- code -----------------------------------------------------------------
#
# A command is (name, block size). The size is the number of codels in the
# block the command is executed *from*, which is what `push` pushes.

def op(name): return [(name, 1)]

def push(n):
    """Push n by leaving a block of n codels."""
    assert n >= 1
    return [('push', n)]

def push0():
    """Zero, which has no block of its own size."""
    return push(1) + op('not')

def width(code): return sum(n for _, n in code)

def pushval(n):
    """Push n as cheaply as the corridor allows: either one block of n
    codels, or a square built with `dup`/`mul` plus a small correction."""
    best = push(n)
    root = int(n ** 0.5)
    for base in (root, root + 1):
        if base < 2: continue
        square = base * base
        core = push(base) + op('dup') + op('mul')
        if square == n: candidate = core
        elif square < n: candidate = core + push(n - square) + op('add')
        else: candidate = core + push(square - n) + op('sub')
        if width(candidate) < width(best): best = candidate
    return best

def print_string(s):
    """Print s, reaching each character from the one before by adding or
    subtracting the difference. `out(char)` pops, so every character is
    duplicated before it is printed; a final `pop` clears the stack."""
    out, prev = [], None
    for ch in s:
        n = ord(ch)
        if prev is None: out += pushval(n)
        elif n > prev: out += pushval(n - prev) + op('add')
        elif n < prev: out += pushval(prev - n) + op('sub')
        out += op('dup') + op('outchar')
        prev = n
    return out + op('pop')

def runs(start, code):
    """The codels of `code` laid end to end, plus the block it finishes in."""
    cells, codel = [], start
    for name, size in code:
        cells += [codel] * size
        codel = advance(codel, name)
    return cells + [codel], codel

# --- layouts --------------------------------------------------------------

START = (0, 1)          # normal red, where every generated program begins

def linear_grid(code, terminal=(1, 1)):
    """Straight-line code in a three-row corridor.

    The first block is the vertical pair at the left edge; the `pop` that
    leaves it is ignored on the empty stack, and its blocked upper exit
    toggles the CC so that execution runs along the middle row."""
    path, _ = runs(advance(START, 'pop'), code)
    middle = [START] + path + ['W', terminal]
    w = len(middle)
    top = [START] + ['B'] * (w - 2) + [terminal]
    bottom = ['B'] * (w - 1) + [terminal]
    return [top, middle, bottom]

def loop_grid(prologue, body, exit_op='pop', loop_op='pop', terminal=(1, 2)):
    """A loop. `body` must end with `pointer`; the value it pops chooses
    between the return corridor (1) and the way out (0)."""
    pro, _ = runs(START, prologue)
    path, pivot = runs(START, body)
    a, l = len(pro), len(path)
    top = ['W'] + pro + ['W'] + path + [advance(pivot, exit_op), 'W', terminal]
    middle = (['B'] * (a + 1) + ['W'] + ['B'] * (l - 1)
              + [advance(pivot, loop_op), 'B', terminal, terminal])
    bottom = ['B'] * (a + 1) + ['W'] * (l + 1) + ['B', 'B', 'B']
    assert len(top) == len(middle) == len(bottom)
    return [top, middle, bottom]

def to_ppm3(rows):
    w, h = len(rows[0]), len(rows)
    out = ['P3', f'{w} {h}', '255']
    for row in rows:
        out.append(' '.join('%d %d %d' % rgb(c) for c in row))
    return '\n'.join(out) + '\n'

# --- the programs ---------------------------------------------------------

def count():
    """Print 1 to 10, one per line: the smallest interesting loop."""
    body = (push(1) + op('add')                       # n := n + 1
            + op('dup') + op('outnum')                # print it
            + push(10) + op('outchar')                # newline
            + op('dup') + push(10) + op('sub')        # n - 10
            + op('not') + op('not')                   # 1 while n /= 10
            + op('dup') + op('pointer'))
    return loop_grid(push0(), body)

def truth():
    """The truth-machine: print 0 and stop, or print 1 for ever."""
    body = (op('dup') + op('outnum')                  # print n
            + op('dup') + op('dup') + op('pointer'))  # loop iff n = 1
    return loop_grid(op('innum'), body)

def collatz():
    """Read n and print its hailstone sequence down to 1.

    The step is branch-free: with r = n mod 2, both cases are
    (n * (1 + 2r) + r) / (2 - r), which is n/2 when r = 0 and 3n + 1 when
    r = 1. That costs one `mod`, one `div` and two `roll`s, and saves a
    second branch in a language where a branch is a change of direction."""
    step = (op('dup') + push(2) + op('mod')                 # [n, r]
            + op('dup') + op('dup')                         # [n, r, r, r]
            + push(2) + op('mul') + push(1) + op('add')     # [n, r, r, 2r+1]
            + push(4) + push(3) + op('roll')                # [r, r, 2r+1, n]
            + op('mul') + op('add')                         # [r, n(2r+1)+r]
            + push(2) + push(1) + op('roll')                # [num, r]
            + op('not') + push(1) + op('add')               # [num, 2-r]
            + op('div'))                                    # [n']
    body = (op('dup') + op('outnum')                        # print n
            + push(10) + op('outchar')                      # newline
            + op('dup') + push(1) + op('sub')
            + op('not') + op('not')                         # [n, n /= 1]
            + push(2) + push(1) + op('roll')                # [flag, n]
            + step                                          # [flag, n']
            + push(2) + push(1) + op('roll')                # [n', flag]
            + op('dup') + op('pointer'))
    return loop_grid(op('innum'), body)

def mondrian(height=34):
    """A program that is also a painting.

    The three rows at the top print `Piet`. Everything below the black band
    is decoration: the pointer never reaches it, so it costs the program
    nothing and constrains it not at all. Piet's normal red, yellow and blue
    are the primaries, which is convenient for the joke."""
    program = linear_grid(print_string('Piet'))
    w = len(program[0])
    rows = [list(program[y]) for y in range(3)]
    rows += [['B'] * w, ['B'] * w]                # the line under the code
    rows += [['W'] * w for _ in range(height - 5)]

    def fill(x0, y0, x1, y1, codel):
        for y in range(y0, y1 + 1):
            for x in range(x0, x1 + 1):
                rows[y][x] = codel

    for x0, x1, y0, y1 in [(14, 15, 5, height - 1), (32, 33, 5, height - 1),
                           (24, 25, 5, 13), (34, 35, 27, height - 1),
                           (0, w - 1, 14, 15), (0, w - 1, 25, 26)]:
        fill(x0, y0, x1, y1, 'B')
    for x0, x1, y0, y1, c in [(34, w - 1, 5, 13, RED), (26, 31, 5, 13, YELLOW),
                              (0, 13, 16, 24, BLUE), (36, w - 1, 16, 24, BLUE),
                              (0, 13, 27, height - 1, RED),
                              (16, 31, 27, height - 1, YELLOW)]:
        fill(x0, y0, x1, y1, c)
    return rows

PROGRAMS = {'count': count, 'truth': truth,
            'collatz': collatz, 'mondrian': mondrian}

def main(argv):
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    for name, build in PROGRAMS.items():
        rows = build()
        rel = os.path.join('Langlib', 'Examples', 'Piet', name + '.ppm')
        with open(os.path.join(root, rel), 'w') as f:
            f.write(to_ppm3(rows))
        print(f'{rel}: {len(rows[0])}x{len(rows)} codels')
    return 0

if __name__ == '__main__':
    raise SystemExit(main(sys.argv))
