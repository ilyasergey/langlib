#!/usr/bin/env python3
"""Generate the original MU runtime demonstrations; --check detects drift."""
import argparse
from pathlib import Path


def word_for(opcode: int, address: int) -> int:
    word = (opcode - address) % 94
    return word if word >= 33 else word + 94


def program(grow: bool) -> bytes:
    # Entry prologue, two reusable working blocks, and data records.
    cells = {
        0: 40, 1: 39, 2: 96, 41: 2998,
        153: 74, 154: 38, 248: 74, 249: 37,
        2998: 248, 2999: 435 if grow else 152,
        3000: 1 if grow else 243, 3001: 153, 3002: 247, 3003: 2997,
    }
    if grow:
        # Enter via two nops at 151 and 152, leaving the return record intact.
        # Grow, walk to a fixed fill phase, return through that fill, halt.
        cells.update({41: 2996, 2997: 150, 436: 74, 440: 70, 441: word_for(81, 441)})
    words = [cells.get(i, word_for(68, i)) for i in range(3004)]
    assert all(n not in (9, 10, 11, 12, 13, 32) for n in words)
    assert all(n < 33 or n > 126 or (n + i) % 94 in (4, 5, 23, 39, 40, 62, 68, 81)
               for i, n in enumerate(words))
    return ("".join(map(chr, words)) + "\n").encode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    for name, grow in (("rotation-loop.mu", False), ("grow-once.mu", True)):
        path = root / "Langlib/Examples/MalbolgeUnshackled" / name
        data = program(grow)
        if args.check:
            if not path.exists() or path.read_bytes() != data:
                raise SystemExit(f"stale runtime example: {path}")
        else:
            path.write_bytes(data)


if __name__ == "__main__":
    main()
