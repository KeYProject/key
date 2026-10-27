#!/usr/bin/env python3
"""Collect the javadoc diagnostics (errors/warnings) of all modules and group them.

Runs the per-module `javadoc` tasks (cap raised via `-Xmaxerrs`/`-Xmaxwarns`,
see the root build.gradle), parses the tool's output and writes a report that
groups the diagnostics by severity (error/warning), then by module and source
file.

The full report is written to `build/warnings/javadoc.md`; a compact summary
is printed to stdout. Extra arguments are forwarded to the Gradle invocation,
e.g. `--offline`. Pass `--no-build` to only re-parse the last captured log
without re-running Gradle.

Gradle skips up-to-date `javadoc` tasks, so on a warm build directory some
modules' diagnostics would be missing from the log. The collector therefore
forces a full re-run (`--rerun-tasks`), making the inventory complete and
reproducible; pass `--incremental` to accept the incremental state instead
(only for quick single-module checks — the counts are then NOT a full
inventory).

Usage:
    python3 scripts/collect-javadoc.py [gradle args...]
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
LOG = OUT_DIR / "javadoc.log"
REPORT = OUT_DIR / "javadoc.md"

# e.g. /abs/path/key.core/src/main/java/de/uka/.../Foo.java:123: error: msg
# or   /abs/path/key.core/src/main/.../Bar.java:7: warning: msg
# or   warning: reference not found: X                (no location)
DIAG_RE = re.compile(
    r"^(?P<file>\S+\.java):(?P<line>\d+): (?P<sev>error|warning): (?P<msg>.*)$"
)
NOLOC_RE = re.compile(r"^(?P<sev>error|warning): (?P<msg>.*)$")

# javac lint warnings are tagged with their category, e.g. '[deprecation]',
# '[serial]', '[unchecked]'. The `javadoc` task depends on `compileJava`, so on
# a cold build directory (fresh clone/worktree) the compile's lint warnings
# land in the same log. They are NOT javadoc diagnostics: javadoc messages
# never carry a '[category]' tag. Exclude them so the inventory is reproducible
# regardless of build-directory state.
LINT_TAG_RE = re.compile(r"^\[[a-z][a-z-]*\]")

# Severities we accept; a bare "N errors"/"N warnings" task summary line is
# not a diagnostic and is skipped.
SEVERITIES = ("error", "warning")
SUMMARY_RE = re.compile(r"^\d+ (error|warning)s?$")


def module_of(path: Path) -> str:
    """First path component relative to the repo root, e.g. 'key.core'."""
    try:
        rel = path.resolve().relative_to(ROOT.resolve())
        return rel.parts[0] if rel.parts else "(root)"
    except ValueError:
        return "(outside repo)"


def relativize(path: str) -> str:
    """Return the path relative to the repo root (fall back to the absolute path)."""
    try:
        return str(Path(path).resolve().relative_to(ROOT.resolve()))
    except ValueError:
        return path


def parse(log_path: Path):
    """Return (diags, unmatched) where diags is a list of dicts.

    Diagnostics without a file:line location (javadoc reports some reference
    errors without one) are kept with file="(no location)".
    """
    diags = []
    unmatched = []
    skipped_lint = 0
    for line in log_path.read_text(errors="replace").splitlines():
        strip = line.strip()
        m = DIAG_RE.match(strip)
        if m and m.group("sev") in SEVERITIES:
            msg = m.group("msg").strip()
            if LINT_TAG_RE.match(msg):
                skipped_lint += 1
                continue
            diags.append(
                {
                    "file": m.group("file"),
                    "line": int(m.group("line")),
                    "sev": m.group("sev"),
                    "msg": msg,
                }
            )
            continue
        m = NOLOC_RE.match(strip)
        if m and m.group("sev") in SEVERITIES and not SUMMARY_RE.match(m.group("msg").strip()):
            msg = m.group("msg").strip()
            if LINT_TAG_RE.match(msg):
                skipped_lint += 1
                continue
            diags.append(
                {
                    "file": "(no location)",
                    "line": 0,
                    "sev": m.group("sev"),
                    "msg": msg,
                }
            )
            continue
        if re.search(r"\bwarning(s)?\b", line, re.IGNORECASE):
            unmatched.append(line.strip())
    return diags, unmatched, skipped_lint


def severity_key(sev: str) -> int:
    return 0 if sev == "error" else 1


def main() -> None:
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    args = list(sys.argv[1:])
    no_build = "--no-build" in args
    if no_build:
        args.remove("--no-build")
    incremental = "--incremental" in args
    if incremental:
        args.remove("--incremental")

    cmd = ["./gradlew", "--console=plain", "javadoc"]
    if not incremental:
        # Force every module's javadoc task to re-run so the log contains the
        # full inventory (up-to-date tasks would silently omit their modules).
        cmd.append("--rerun-tasks")
    cmd.extend(args)
    if not no_build:
        print("running:", " ".join(cmd))
        with LOG.open("w") as out:
            result = subprocess.run(cmd, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
        print(f"gradlew exit code: {result.returncode} (full output in {LOG})")
    else:
        print("skipping build, parsing existing", LOG)

    diags, unmatched, skipped_lint = parse(LOG)
    if not diags:
        print("no diagnostics parsed from", LOG)
        if unmatched:
            print("unmatched diagnostic-like lines:")
            for u in unmatched[:20]:
                print("  ", u)
        sys.exit(1)

    errors = [d for d in diags if d["sev"] == "error"]
    warnings = [d for d in diags if d["sev"] == "warning"]
    by_module = collections.Counter(module_of(Path(d["file"])) for d in diags)
    detail = collections.Counter(
        (d["sev"], module_of(Path(d["file"])), d["file"]) for d in diags
    )
    modules = sorted(by_module)

    with REPORT.open("w") as rep:
        rep.write("# KeY javadoc diagnostics inventory\n\n")
        rep.write(f"* generated: {datetime.now(timezone.utc).isoformat()}\n")
        rep.write(f"* command: `{' '.join(cmd)}`\n\n")
        rep.write(f"Total diagnostics: **{len(diags)}** (**{len(errors)}** errors, "
                  f"**{len(warnings)}** warnings) across **{len(modules)}** modules.\n\n")

        rep.write("## Summary by severity\n\n")
        rep.write("| severity | count |\n|---|---|\n")
        rep.write(f"| error | {len(errors)} |\n")
        rep.write(f"| warning | {len(warnings)} |\n\n")

        rep.write("## Summary by module\n\n")
        rep.write("| module | errors | warnings | total |\n|---|---|---|---|\n")
        for mod, n in sorted(by_module.items(), key=lambda kv: (-kv[1], kv[0])):
            e = sum(1 for d in diags if d["sev"] == "error" and module_of(Path(d["file"])) == mod)
            w = n - e
            rep.write(f"| {mod} | {e} | {w} | {n} |\n")
        rep.write("\n")

        rep.write("## Details (grouped by severity, module, file)\n\n")
        by_sev_mod_file = collections.defaultdict(collections.Counter)
        for (sev, mod, file_), n in detail.items():
            by_sev_mod_file[sev][(mod, file_)] += n

        for sev in SEVERITIES:
            if not by_sev_mod_file[sev]:
                continue
            rep.write(f"### {sev} ({len([d for d in diags if d['sev'] == sev])})\n\n")
            current_module = None
            for (mod, file_), n in sorted(
                by_sev_mod_file[sev].items(), key=lambda kv: (-kv[1], kv[0][0], kv[0][1])
            ):
                if mod != current_module:
                    current_module = mod
                    rep.write(f"* **{mod}**\n")
                rep.write(f"  * `{relativize(file_)}` — {n}\n")
            rep.write("\n")

    print(f"report written to {REPORT}")
    print("\nSeverities (most first):")
    for sev, n in (("error", len(errors)), ("warning", len(warnings))):
        print(f"  {n:6d}  {sev}")
    print(f"\ntotal: {len(diags)} diagnostics")
    if skipped_lint:
        print(f"(info: {skipped_lint} javac lint warnings from the compileJava tasks "
              f"excluded — they are not javadoc diagnostics)")
    if unmatched:
        print(f"(info: {len(unmatched)} unparsed diagnostic-like lines, "
              f"e.g. summary lines without a location)")


if __name__ == "__main__":
    main()
