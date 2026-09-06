#!/usr/bin/env python3
"""Compare JavaGen subtype/result queries with a real Java compiler."""

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile

from javagen_java import ROOT, DEFAULT_RUNNER, check_query, export, find_javac, invoke


def cases():
    examples = ROOT / "Langlib/Examples/JavaGen"
    for name in ["reflexive", "contravariant", "ground", "diamond", "rejected"]:
        yield name, (examples / f"{name}.jgen").read_text(), name != "rejected", None
    hierarchy = ("zero Z; interface P<x> {} interface C<x> extends P<x> {} "
                 "interface S<x> {} ")
    for name, lhs, rhs, accepted in [
        ("inherit", "C<Z>", "P<Z>", True),
        ("reverse-inherit", "P<Z>", "C<Z>", False),
        ("nested-positive", "S<S<C<Z>>>", "S<S<P<Z>>>", True),
        ("nested-negative", "S<S<P<Z>>>", "S<S<C<Z>>>", False),
        ("different-depth", "S<Z>", "S<S<Z>>", False),
        ("zero-to-unary", "Z", "P<Z>", False),
        ("unary-to-zero", "P<Z>", "Z", False),
    ]:
        yield name, hierarchy + f"check {lhs} <: {rhs};", accepted, None
    yield "ground-in-path", ("zero Z; interface C<x> extends M<M<Z>> {} "
                            "interface M<x> extends Z {} check C<M<Z>> <: Z;"), True, None
    yield "java-keywords", ("zero Z; interface class<x> {} interface public<x> "
                            "extends class<x> {} check public<Z> <: class<Z>;"), True, None
    # The candidate must matter: for every arithmetic result check a wrong neighbor too.
    for n in [1, 2, 3, 5, 10]:
        numeral = "Succ<" + "Pad<Succ<" * (n - 1) + "Z" + ">" * (2 * n - 1)
        source = ("zero Z; interface Succ<x> {} interface Pad<x> {} interface Result<x> {} "
                  "interface AddTwo<x> extends Result<Succ<Pad<Succ<Pad<x>>>>> {} "
                  f"check AddTwo<{numeral}> <: Result<answer>;")
        yield f"add-two-{n}", source, True, n + 2
    yield "zero-answer", (examples / "zero-answer.jgen").read_text(), True, 0
    for name, result in [("fib", 55), ("fact", 120), ("sum", 55)]:
        yield name, (examples / f"{name}.jgen").read_text(), True, result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-javac", action="store_true")
    parser.add_argument("--javac", default="javac")
    parser.add_argument("--runner", type=Path, default=DEFAULT_RUNNER)
    parser.add_argument("--timeout", type=float, default=15)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    javac, version = find_javac(args.javac, args.timeout)
    if javac is None:
        print(("FAIL " if args.require_javac else "SKIP ") + version)
        return 1 if args.require_javac else 0
    runner = args.runner.resolve()
    if not runner.is_file():
        print("FAIL build the evaluator first: lake build javagen")
        return 1
    print("JavaGen conformance against " + version)
    passed = failed = inconclusive = 0
    with tempfile.TemporaryDirectory(prefix="javagen-conformance-") as temp:
        directory = Path(temp)
        for name, text, accepted, answer in cases():
            source = directory / f"{name}.jgen"
            source.write_text(text)
            try:
                lean = invoke([str(runner), "--fuel", "1000", str(source)], args.timeout)
                if lean.returncode not in (0, 1):
                    raise ValueError("evaluator gave no verdict: " + lean.stderr.strip())
                if (lean.returncode == 0) != accepted:
                    raise ValueError("evaluator disagrees with expected verdict")
                if answer is not None and lean.stdout != f"{answer}\n":
                    raise ValueError(f"expected answer {answer}, got {lean.stdout!r}")
                declarations = export(runner, source, args.timeout, declarations=True)
                candidates = [(answer, accepted)]
                if answer is not None:
                    candidates.append((answer + 1, False))
                for candidate, want in candidates:
                    label = name + (f"/answer-{candidate}" if candidate is not None else "")
                    query = export(runner, source, args.timeout, answer=candidate)
                    verdict = check_query(javac, declarations, query,
                                          directory / label, args.timeout)
                    if verdict.kind == ("accept" if want else "reject"):
                        passed += 1
                        print("PASS " + label)
                    elif verdict.kind == "inconclusive":
                        inconclusive += 1
                        print(f"INCONCLUSIVE {label}: {verdict.detail[:1000]}")
                    else:
                        failed += 1
                        print(f"FAIL {label}: {verdict.kind}: {verdict.detail[:1000]}")
            except subprocess.TimeoutExpired:
                inconclusive += 1
                print(f"INCONCLUSIVE {name}: evaluator or exporter timeout")
            except (OSError, ValueError) as error:
                failed += 1
                print(f"FAIL {name}: {error}")
    print(f"{passed} passed, {failed} failed, {inconclusive} inconclusive")
    return 1 if failed else 2 if inconclusive else 0


if __name__ == "__main__":
    sys.exit(main())
