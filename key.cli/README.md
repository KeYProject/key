# Module: KeY Headless CLI (`key.cli`)

Headless command-line interface to the KeY verifier for scripts and LLM agents: prove JML
contract obligations of `.key` problem files or plain Java sources, list a problem's contracts,
execute line-oriented proof scripts against one obligation, and replay saved proofs. Use it
whenever KeY verification must run without the GUI — from a build, a CI job, or an agent —
where you can rely on the exact flags, the byte-exact `KEY_RESULT` JSON record on stdout, the
exit-code contract (0 closed / 1 open / 2 timed_out / 3 input error / 4 internal error), and
the structured `KEY_ERROR` diagnostics on stderr. Run with `./gradlew :key.cli:shadowJar` then
`java -jar key.cli/build/libs/key-cli.jar <subcommand> [args]`; the subcommands are `prove`,
`list`, `script`, and `replay`. The normative interface contract is
[`docs/superpowers/specs/2026-11-14-key-cli-interface-spec.md`](../docs/superpowers/specs/2026-11-14-key-cli-interface-spec.md)
(§1–§11); the user-facing documentation is
[`docs/cli.md`](../docs/cli.md).

The entry point is `org.key_project.key.cli.Main` (a picocli root command). Subcommands:

| Subcommand | Purpose |
|---|---|
| `prove <files>…` | Prove the selected contracts; one `KEY_RESULT` JSON line per contract on stdout. Selection via `--choose-contract`, proof output via `--proof`/`--proof-dir` (with `--save-partial`), open-goal printing via `--print-open-goals [MAX]`, search bound via `--timeout`, run settings via `--settings-file`/`--strategy-option`. |
| `list <files>…` | Print one tab-separated `<IDX>\t<target>\t<NAME>` line per contract in stable index order (0-based, restarting per file); exits 0 on success and never prints a `KEY_RESULT` line. |
| `script <load-file> <script-file>` | Execute a line-oriented §7.1 proof script against exactly one selected obligation; `SCRIPT OK`/`SCRIPT FAIL`/`SCRIPT FINAL` lines plus one `KEY_RESULT` record. |
| `replay <proof>` | Replay a saved proof; an incompatible proof is an input error (exit 3). |

All subcommands share the §1 exit-code contract and report every CLI-level error as a single
line-oriented `KEY_ERROR` on stderr.
