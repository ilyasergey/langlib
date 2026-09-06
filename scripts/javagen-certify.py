#!/usr/bin/env python3
"""Infer a JavaGen natural answer, then verify its original query with javac."""

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile

from javagen_java import DEFAULT_RUNNER, check_query, export, find_javac, invoke


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--runner", type=Path, default=DEFAULT_RUNNER)
    parser.add_argument("--javac", default="javac")
    parser.add_argument("--fuel", type=int, default=100_000)
    parser.add_argument("--timeout", type=float, default=15,
                        help="seconds per subprocess (default: 15)")
    args = parser.parse_args()
    if args.fuel < 0 or args.timeout <= 0:
        parser.error("fuel must be nonnegative and timeout must be positive")
    source, runner = args.source.resolve(), args.runner.resolve()
    if not runner.is_file():
        print("Build the evaluator first: lake build javagen", file=sys.stderr)
        return 3
    javac, version = find_javac(args.javac, args.timeout)
    if javac is None:
        print("No certification: " + version, file=sys.stderr)
        return 3
    try:
        evaluated = invoke([str(runner), "--fuel", str(args.fuel), str(source)], args.timeout)
        if evaluated.returncode:
            print(evaluated.stderr.strip(), file=sys.stderr)
            return evaluated.returncode if evaluated.returncode in (1, 2, 3) else 2
        candidate = evaluated.stdout.strip()
        if not candidate.isascii() or not candidate.isdecimal():
            raise ValueError("certification requires a numeric answer query, not a closed check")
        # Specialize the original computation; never replace it with a literal-result program.
        declarations = export(runner, source, args.timeout, declarations=True)
        query = export(runner, source, args.timeout, answer=candidate)
        with tempfile.TemporaryDirectory(prefix="javagen-certify-") as temp:
            verdict = check_query(javac, declarations, query, Path(temp), args.timeout)
        if verdict.kind != "accept":
            print(f"No certification ({verdict.kind}): {verdict.detail}", file=sys.stderr)
            return 2 if verdict.kind == "inconclusive" else 1
        print(f"answer: {candidate}\njavac: accepted ({version})")
        return 0
    except subprocess.TimeoutExpired:
        print("No certification: evaluator or exporter timed out", file=sys.stderr)
        return 2
    except (OSError, ValueError) as error:
        print(f"No certification: {error}", file=sys.stderr)
        return 3


if __name__ == "__main__":
    sys.exit(main())
