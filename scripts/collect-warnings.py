#!/usr/bin/env python3
"""Collect the javac (lint) warnings of a full build and group them into categories.

Compiles all main and test sources with warnings enabled (see the root
build.gradle, `-Xlint:all` in the shared JavaCompile configuration), parses the
compiler output and writes a report that groups the warnings by their lint
category (e.g. `deprecation`, `unchecked`, `rawtypes`, ...), then by module and
source file.

The full report is written to `build/warnings/warnings.md`; a compact summary
is printed to stdout. Extra arguments are forwarded to the Gradle invocation,
e.g. `--offline` or `--rerun-tasks` (use the latter if a previous compile is
up to date and you want to force a fresh run).

Usage:
    python3 scripts/collect-warnings.py [gradle args...]
"""

import collections
import pathlib
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT_DIR = ROOT / "build" / "warnings"
LOG = OUT_DIR / "compile.log"
REPORT = OUT_DIR / "warnings.md"

# e.g. /abs/path/key.core/src/main/java/de/uka/.../Foo.java:123: warning: [deprecation] msg
# The category brackett is optional; warnings without one are grouped as "other".
WARN_RE = re.compile(
    r"^(?P<file>\S+\.java):(?P<line>\d+): warning: (\[(?P<cat>[a-z-]+)\])?(?P<msg>.*)$"
)


def module_of(path: Path) -> str:
    """First path component relative to the repo root, e.g. 'key.core'."""
    try:
        rel = path.resolve().relative_to(ROOT.resolve())
        return rel.parts[0] if rel.parts else "(root)"
    except ValueError:
        return "(outside repo)"


def parse(log_path: Path):
    """Return (warnings, unmatched) where warnings is a list of dicts."""
    warnings = []
    unmatched = []
    for line in log_path.read_text(errors="replace").splitlines():
        m = WARN_RE.match(line.strip())
        if not m:
            continue
        warnings.append(
            {
                "file": m.group("file"),
                "line": int(m.group("line")),
                "cat": m.group("cat") or "other",
                "msg": m.group("msg").strip(),
            }
        )
    return warnings


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    args = list(sys.argv[1:])
    no_build = "--no-build" in args
    if no_build:
        args.remove("--no-build")

    cmd = ["./gradlew", "--console=plain", "testClasses", *args]
    if not no_build:
        print("running:", " ".join(cmd))
        with LOG.open("w") as out:
            result = subprocess.run(cmd, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
        print(f"gradlew exit code: {result.returncode} (full output in {LOG})")
    else:
        print("skipping build, parsing existing", LOG)

    warnings = parse(LOG)
    if not warnings:
        print("no warnings parsed from", LOG)
        sys.exit(1)

    by_cat = collections.Counter(w["cat"] for w in warnings)
    by_module = collections.Counter(module_of(Path(w["file"])) for w in warnings)
    # (category, module, file) -> count, for the detail sections
    detail = collections.Counter(
        (w["cat"], module_of(Path(w["file"])), w["file"]) for w in warnings
    )
    modules = sorted(by_module)

    with REPORT.open("w") as rep:
        rep.write("# KeY compiler warning inventory\n\n")
        rep.write(f"* generated: {datetime.now(timezone.utc).isoformat()}\n")
        rep.write(f"* command: `{' '.join(cmd)}`\n\n")
        rep.write(f"Total warnings: **{len(warnings)}** across **{len(modules)}** modules, "
                  f"in **{len(by_cat)}** categories.\n\n")

        rep.write("## Summary by category\n\n")
        rep.write("| category | count |\n|---|---|\n")
        for cat, n in sorted(by_cat.items(), key=lambda kv: (-kv[1], kv[0])):
            rep.write(f"| {cat} | {n} |\n")
        rep.write("\n")

        rep.write("## Summary by module\n\n")
        rep.write("| module | count |\n|---|---|\n")
        for mod, n in sorted(by_module.items(), key=lambda kv: (-kv[1], kv[0])):
            rep.write(f"| {mod} | {n} |\n")
        rep.write("\n")

        rep.write("## Details (grouped by category, module, file)\n\n")
        by_cat_mod_file = collections.defaultdict(collections.Counter)
        for (cat, mod, file_), n in detail.items():
            by_cat_mod_file[cat][(mod, file_)] += n

        for cat in sorted(by_cat_mod_file, key=lambda c: (-by_cat[c], c)):
            rep.write(f"### {cat} ({by_cat[cat]})\n\n")
            current_module = None
            for (mod, file_), n in sorted(
                by_cat_mod_file[cat].items(), key=lambda kv: (-kv[1], kv[0][0], kv[0][1])
            ):
                if mod != current_module:
                    current_module = mod
                    rep.write(f"* **{mod}**\n")
                rep.write(f"  * `{file_}` — {n}\n")
            rep.write("\n")

    print(f"report written to {REPORT}")
    print("\nCategories (most warnings first):")
    for cat, n in sorted(by_cat.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"  {n:6d}  {cat}")
    print(f"\ntotal: {len(warnings)} warnings")


if __name__ == "__main__":
    main()
