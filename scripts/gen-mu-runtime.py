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


def repeated_growth() -> bytes:
    # Finite startup synthesizes the three initially non-printable RNops.
    # Two calls use distinct one-markers but the same growth and reset code.
    cells = {
        0: 40, 1: 39, 2: 96, 41: 4199, 4200: 999, 4201: 3099,
        153: 74, 154: 38, 248: 74, 249: 37, 341: 74, 342: 38,
        436: 74, 437: 2267, 438: 180, 439: 6567, 440: 70, 441: 33,
        3100: 2265, 3101: 436, 181: 3103, 3104: 217, 3105: 437,
        6568: 3107, 3108: 6561, 3109: 438, 71: 2996,
        2997: 150, 2998: 248, 2999: 435,
        3000: 1, 3001: 153, 3002: 247, 3003: 2997,
        3197: 338, 3198: 248, 3199: 435,
        3200: 1, 3201: 341, 3202: 247, 3203: 3197,
        5002: 436, 5007: 1199, 5008: 3196, 5009: 1299,
        1200: word_for(40, 1200), 1201: word_for(4, 1201),
        1300: word_for(81, 1300), 7000: 5001, 7001: 5001,
    }
    startup = [40, 62, 40, 62, 40, 40, 62, 40, 62,
               40, 40, 62, 40, 62, 40, 40, 4]
    cells.update({1000 + i: word_for(op, 1000 + i) for i, op in enumerate(startup)})
    words = [cells.get(i, word_for(68, i)) for i in range(7002)]
    assert all(n not in (9, 10, 11, 12, 13, 32) for n in words)
    assert all(n < 33 or n > 126 or (n + i) % 94 in (4, 5, 23, 39, 40, 62, 68, 81)
               for i, n in enumerate(words))
    return ("".join(map(chr, words)) + "\n").encode("utf-8")


def marker_reset() -> bytes:
    # Bootstrap the all-ones constants and the mask, rotate the same marker,
    # then call the restored reset again. No input or fresh marker is used.
    cells = {
        0: 40, 1: 39, 2: 96, 41: 4199, 4200: 999, 4201: 2999,
        39: 3099, 110: 3599, 2999: 152, 75: 2998,
        153: 74, 154: 38, 248: 74, 249: 37, 270: 74, 271: 109,
        530: 74, 531: 37,
        3000: 243, 3001: 153, 3002: 247, 3003: 3197,
        3100: 243, 3101: 3399,
        3198: 248, 3199: 269, 3200: 243, 3201: 270, 3202: 529,
        3203: 3398, 3204: 1299, 3205: 3199, 3211: 1399,
        3399: 269, 3400: 243, 3401: 270, 3402: 247, 3403: 3497,
        3498: 248, 3499: 269, 3500: 2, 3501: 270, 3502: 247, 3503: 3597,
        3598: 248, 3599: 269, 3600: 243, 3601: 270, 3602: 247, 3603: 3197,
        1400: word_for(81, 1400),
    }
    startup = [40, 62, 40, 40, 40, 62, 40, 62, 40, 40, 40, 62, 68, 40, 40, 40, 4]
    cells.update({1000 + i: word_for(op, 1000 + i) for i, op in enumerate(startup)})
    # On the second visit the first six encrypted words are all no-ops;
    # the stable jump then selects the separate halt record.
    prepare = [40, 39, 68, 40, 40, 40, 4]
    cells.update({1300 + i: word_for(op, 1300 + i) for i, op in enumerate(prepare)})
    words = [cells.get(i, word_for(68, i)) for i in range(4202)]
    assert all(n not in (9, 10, 11, 12, 13, 32) for n in words)
    assert all(n < 33 or n > 126 or (n + i) % 94 in (4, 5, 23, 39, 40, 62, 68, 81)
               for i, n in enumerate(words))
    return ("".join(map(chr, words)) + "\n").encode("utf-8")


def marker_cycle() -> bytes:
    # Extend the reset layout with the shared rotor and two reusable routes.
    # Bootstrap three no-ops before building the reset's resident constants.
    words = list(map(ord, marker_reset().decode("utf-8").removesuffix("\n")))
    for i in [*range(1301, 1307), 1400, 3211]:
        words[i] = word_for(68, i)
    cells = {
        4201: 3799, 3800: 6617, 3801: 525,
        526: 127, 527: 2224, 528: 2467, 529: 74,
        2225: 6598, 2226: 526, 2468: 6598, 2469: 527,
        3000: 317, 83: 3599, 110: 82,
        272: 247, 273: 2995, 2996: 248, 2997: 529,
        1300: 114, 3205: 247, 3206: 3194, 3195: 248, 3196: 525,
    }
    # Synthesize 526, 527, 528; load all-ones; continue constant bootstrap.
    startup = [40, 62, 40, 62, 40, 62, 40, 62, 40, 62, 40, 62,
               40, 40, 68, 62,
               40, 40, 40, 62, 40, 62, 40, 40, 40, 40, 62, 68, 40, 40, 40, 4]
    cells.update({1000 + i: word_for(op, 1000 + i) for i, op in enumerate(startup)})
    for i, v in cells.items():
        words[i] = v
    assert all(n not in (9, 10, 11, 12, 13, 32) for n in words)
    assert all(n < 33 or n > 126 or (n + i) % 94 in (4, 5, 23, 39, 40, 62, 68, 81)
               for i, n in enumerate(words))
    return ("".join(map(chr, words)) + "\n").encode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    for name, data in (("rotation-loop.mu", program(False)),
                       ("grow-once.mu", program(True)),
                       ("grow-twice.mu", repeated_growth()),
                       ("marker-reset.mu", marker_reset()),
                       ("marker-cycle.mu", marker_cycle())):
        path = root / "Langlib/Examples/MalbolgeUnshackled" / name
        if args.check:
            if not path.exists() or path.read_bytes() != data:
                raise SystemExit(f"stale runtime example: {path}")
        else:
            path.write_bytes(data)


if __name__ == "__main__":
    main()
