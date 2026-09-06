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


def growing_marker() -> bytes:
    # The same marker drives every growth. A finite startup at 8000
    # initializes all no-op orbits, then constructs the reset constants.
    base = list(map(ord, marker_cycle().decode("utf-8").removesuffix("\n")))
    words = base + [word_for(68, i) for i in range(len(base), 12006)]
    for i in range(1000, 1032):
        words[i] = word_for(68, i)
    cells = {
        41: 7799, 7800: 7999, 7801: 5999,
        2999: 1399, 1404: 104, 3004: 247, 3005: 3190,
        3191: 248, 3192: 428, 1200: 120, 5008: 247, 5009: 2990,
        2991: 248, 2992: 145,
        436: 74, 440: 70, 441: 33, 5002: 436, 5007: 1199,
        3000: 317, 3400: 243, 3600: 243, 3200: 1,
        12004: 5001, 12005: 5001,
    }
    cells.update({a: 5999 for a in [39, 42, 52, 61, 71, 75, 83, 97, 103, 105]})
    for i, v in cells.items():
        words[i] = v
    known = dict(enumerate(words))
    code, data, record = 8000, 7801, 0

    def emit(op: int) -> None:
        nonlocal code
        words[code] = word_for(op, code)
        code += 1

    def scratch() -> int:
        nonlocal data, record
        for _ in range(10):
            if data == 6000:
                break
            emit(40)
            data = known[data] + 1
        assert data == 6000
        for _ in range(3 * record):
            emit(68)
            data += 1
        record += 1
        return data

    table = [[1, 1, 2], [0, 0, 2], [0, 2, 1]]

    def pair(a: int, out: int) -> tuple[int, int]:
        x, b, power = 0, 0, 1
        for i in range(9):
            choices = [(u, v) for u in range(3) for v in range(3)
                       if table[table[a % 3][u]][v] == out % 3]
            u, v = (1, 1) if i == 8 else choices[0]
            assert (u, v) in choices
            x += u * power
            b += v * power
            power *= 3
            a //= 3
            out //= 3
        return x, b

    targets = {a: 74 for a in [*range(146, 153), *range(429, 436),
                               *range(526, 529), *range(1400, 1404)]}
    targets.update({435: 41, 437: 41, 438: 102, 439: 96, 1402: 41})
    acc = 0
    for target, value in sorted(targets.items(), reverse=True):
        slot = scratch()
        x, b = pair(acc, value)
        words[slot], words[slot + 1], words[target] = x, target - 1, b
        emit(62)
        emit(40)
        emit(62)
        data, acc, known[target] = target + 1, value, value
    assert acc == 74
    slot = scratch()
    words[slot] = 2999
    emit(40)
    emit(62)  # crz 74 317 = all-ones at 3000
    data = 3001
    for target, operand in [(3400, 243), (3600, 245)]:
        slot = scratch()
        words[slot], words[slot + 1] = operand, target - 1
        emit(62)
        emit(40)
        emit(62)
        data = target + 1
    slot = scratch()
    words[slot] = 5006
    emit(40)
    emit(4)  # enter the shared growth-to-reset route at 1200/5008
    assert code < 12004
    assert all(n not in (9, 10, 11, 12, 13, 32) for n in words)
    assert all(n < 33 or n > 126 or (n + i) % 94 in (4, 5, 23, 39, 40, 62, 68, 81)
               for i, n in enumerate(words))
    return ("".join(map(chr, words)) + "\n").encode("utf-8")


def bit_branch() -> bytes:
    # Synthesize the runtime no-op at address 1, then visit the same branch
    # with flags 0, 1, 1, 0. The callers form a finite chain ending in halt.
    cells = {0: 98, 1: 6635, 2: 96,
             97: 1999, 2000: 0, 2001: 699, 2002: 799, 2003: 9999,
             10000: 1, 10001: 899, 10002: 10099,
             10100: 1, 10101: 999, 10102: 10199,
             10200: 0, 10201: 699, 10202: 699,
             6636: 6561, 6637: 0}
    code = {99: 40, 100: 62, 101: 40, 102: 62, 103: 40, 104: 40, 105: 4,
            700: 81, 800: 40, 801: 4,
            900: 40, 901: 4, 1000: 40, 1001: 4}
    cells.update({i: word_for(op, i) for i, op in code.items()})
    words = [cells.get(i, word_for(68, i)) for i in range(10204)]
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
                       ("marker-cycle.mu", marker_cycle()),
                       ("grow-loop.mu", growing_marker()),
                       ("bit-branch.mu", bit_branch())):
        path = root / "Langlib/Examples/MalbolgeUnshackled" / name
        if args.check:
            if not path.exists() or path.read_bytes() != data:
                raise SystemExit(f"stale runtime example: {path}")
        else:
            path.write_bytes(data)


if __name__ == "__main__":
    main()
