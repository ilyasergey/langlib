"""Shared process boundary for JavaGen's real-javac checks (Python 3 stdlib)."""

from dataclasses import dataclass
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_RUNNER = ROOT / ".lake/build/bin/javagen"


@dataclass
class Verdict:
    kind: str
    detail: str = ""


def invoke(command, timeout):
    return subprocess.run(command, input="", text=True, capture_output=True,
                          timeout=timeout, cwd=ROOT)


def find_javac(requested, timeout):
    executable = shutil.which(requested)
    if not executable:
        return None, f"Java compiler not found: {requested}"
    try:
        version = invoke([executable, "-version"], timeout)
    except (OSError, subprocess.TimeoutExpired) as error:
        return None, f"cannot run {requested}: {error}"
    if version.returncode:
        return None, (version.stdout + version.stderr).strip()
    return executable, (version.stdout + version.stderr).strip()


def export(runner, source, timeout, answer=None, declarations=False):
    args = [str(runner)]
    if answer is not None and not declarations:
        args += ["--answer", str(answer)]
    args += ["--java-declarations" if declarations else "--java", str(source)]
    generated = invoke(args, timeout)
    if generated.returncode:
        raise ValueError("JavaGen export failed: " + generated.stderr.strip())
    return generated.stdout


def compile_java(javac, source, directory, timeout):
    """Accept only an ordinary incompatible-return diagnostic as rejection."""
    directory.mkdir(parents=True, exist_ok=True)
    file = directory / "JavaGenCheck.java"
    file.write_text(source)
    classes = directory / "classes"
    classes.mkdir(exist_ok=True)
    try:
        result = invoke([javac, "-proc:none", "-Xlint:unchecked", "-Werror",
                         "-XDrawDiagnostics", "-d", str(classes), str(file)], timeout)
    except subprocess.TimeoutExpired:
        return Verdict("inconclusive", f"javac exceeded {timeout:g} seconds")
    except OSError as error:
        return Verdict("inconclusive", str(error))
    diagnostics = (result.stdout + result.stderr).strip()
    if result.returncode == 0:
        return Verdict("accept", diagnostics)
    if result.returncode not in (0, 1) or any(marker in diagnostics for marker in
            ["StackOverflowError", "OutOfMemoryError", "An exception has occurred",
             "compiler.err.limit."]):
        return Verdict("inconclusive", diagnostics)
    codes = set(re.findall(r"compiler\.err\.[a-zA-Z0-9_.]+", diagnostics))
    if codes and codes <= {"compiler.err.prob.found.req", "compiler.err.inconvertible.types"}:
        return Verdict("reject", diagnostics)
    return Verdict("invalid", diagnostics)


def check_query(javac, declarations, query, directory, timeout):
    """Declaration failure cannot masquerade as the intended query rejection."""
    baseline = compile_java(javac, declarations, directory / "declarations", timeout)
    if baseline.kind != "accept":
        kind = "inconclusive" if baseline.kind == "inconclusive" else "invalid"
        return Verdict(kind, "declarations did not compile:\n" + baseline.detail)
    return compile_java(javac, query, directory / "query", timeout)
