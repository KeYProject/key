# KeY Headless Interface Specification — precise requirements

Version: 2 (concrete spec — supersedes the draft `keY-interface-requirements.md`)
Date: 2026-11-14
Scope: the public interface of a KeY batch/driver mode that a script or LLM agent can
implement against **with zero ambiguity**. Every format, exit code, and acceptance test
below is byte-level specified so it can be coded and verified automatically.

---

## 0. Conventions

- All examples reference the real project contracts so an implementer can reproduce them:
  `verify/quickheap.key`, `src/main/java/edu/kit/quickheap/QuickHeap.java`, `verify/tools/key-3.0.0/key-3.0.0-exe.jar`.
- `<MS>` is an integer ≥ 0 (0 = no timeout). `<IDX>` is a decimal integer. `<NAME>` is a contract name string (see §4).
- "stdout" = fd 1, "stderr" = fd 2. Result records go to stdout unless stated otherwise.
- All new flags are **additive**; the existing invocation form
  `( echo <IDX> | java -jar key.jar --auto --timeout=<MS> <files…> )` continues to work unchanged,
  but under it the result record (§2) is now **also** printed.
- "Must fail" = process exits non-zero AND prints a `KEY_ERROR` line (§8) explaining why.
- Acceptance tests are run in a headless bash shell. Each test names the exact command and the exact expected bytes/exit code.

---

## 1. Exit-code contract (all batch modes)

| Code | Meaning | Printed result status |
|---|---|---|
| `0`  | bound: one or more contracts, **all** closed | `closed` |
| `1`  | some selected contract not closed (goal remains) | `open` |
| `2`  | abandoned due to timeout (no decision, not "open") | `timed_out` |
| `3`  | input error (file not found, parse error, unknown option, unknown contract, bad settings) | `error` |
| `4`  | internal error (exception not attributable to input) | `error` |

Rules:
- Exit code reflects the **worst** status among selected contracts (e.g. one `closed` + one `open` ⇒ exit `1`).
- `check_exit` tests must assert the exact integer.

Acceptance A1 (trivial closed): file `T.java` = the literal-contract example of §9, run with
`--choose-contract 0` and `--timeout 30000` ⇒ exit `0`, stdout contains the §2 line with `"status":"closed"`.
Acceptance A2 (known open): `/*@ ensures \result == 1; @*/ int f() { return 2; }` ⇒ exit `1`, status `open`, `openGoals ≥ 1`.
Acceptance A3 (timeout): same input with `--timeout 1` ⇒ exit `2`, status `timed_out`.

---

## 2. Machine-readable result record (one line, exact)

In any batch mode, exactly **one** line is written to stdout, and it is the **last** line of stdout.
Its prefix is the literal 11 characters `KEY_RESULT `, followed by a single JSON object (no trailing
whitespace, terminated by `\n`). No other line on stdout may start with `KEY_RESULT`.

```json
KEY_RESULT {"version":1,"contract":"edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::partition([I,int,int,[I)].JML normal_behavior operation contract.0","status":"closed|open|timed_out|error","openGoals":0,"elapsedMs":1234,"proofFile":null,"smtCalls":0,"smtProved":0,"errorMessage":null}
```

Exact schema:

| field | type | semantics |
|---|---|---|
| `version` | int | must be `1` |
| `contract` | string | canonical contract name actually proven (as in §4) |
| `status` | one of `"closed"`, `"open"`, `"timed_out"`, `"error"` | final outcome of this contract |
| `openGoals` | int | number of open goals at termination; `0` iff `status=="closed"` |
| `elapsedMs` | int | wall clock ms of proof search for this contract |
| `proofFile` | string \| null | absolute path of the written proof file, or `null`; see §3 |
| `smtCalls` | int | SMT solver invocations (0 unless SMT enabled, §7) |
| `smtProved` | int | goals proved via SMT (0 unless SMT enabled) |
| `errorMessage` | string \| null | human-readable message; non-null iff `status=="error"` |

- Multiple selected contracts produce **one line per contract**, in selection order; the `KEY_RESULT`
  lines are the last N lines of stdout.
- If no contract was selected (listing mode, §4), no `KEY_RESULT` line is printed.

Acceptance B1: `bash -c '(printf "0\n" | java -jar key.jar --auto --timeout=30000 T.key) | tail -n 1'`
must print a line whose first 11 bytes equal `KEY_RESULT ` and whose remainder parses as the JSON above.
Acceptance B2: for a known-open contract the JSON has `"status":"open"` and `"openGoals">=1` in every run.

---

## 3. Proof-file honesty (write/never-write, content marker)

- Default: a `.proof` file is written **only when** the contract's proof is closed (`status == "closed"`).
- Explicit output location: `--proof <PATH>` (writes the proof there; overridden per contract by `--proof <PATH>` + `--proof-suffix`? — no: `--proof <PATH>` is for single-contract runs; multi-contract runs use `--proof-dir <DIR>` and name files `<contract-index>.proof`).
- `--save-partial`: if given, an unclosed proof MAY be saved; **must** then contain the marker line as first line:
  `KEY_PROOF_STATUS open <openGoals>`
- A closed proof's file **must** start with the marker line:
  `KEY_PROOF_STATUS closed 0`
- No proof file may be written to a location the caller did not request via `--proof`/`--proof-dir` (this kills the current surprise `quickheap.auto.0.proof` behavior). In pure legacy mode (`--auto` without `--proof*`), no proof file is written at all unless a `\proof` block exists in the load file.
- Marker parse rule for consumers: read first line; if it equals `KEY_PROOF_STATUS closed 0` ⇒ treat as closed, else not closed.

Acceptance C1 (open, default): known-open contract, no `--save-partial` ⇒ no new `.proof` file exists anywhere under the run directory (assert with `find . -newer <stamp>`), exit `1`.
Acceptance C2 (open, with `--save-partial`): file starts with `KEY_PROOF_STATUS open ` followed by an integer ≥ 1.
Acceptance C3 (closed): file starts exactly with `KEY_PROOF_STATUS closed 0`; `grep -c 'KEY_PROOF_STATUS closed 0' file` = 1.

---

## 4. Contract selection and listing (deterministic)

### 4.1 The contract name grammar

A contract name is a single line with no newlines, matching:

```
NAME := CLASS "[" METHOD "]" "." KIND ["." INT]
CLASS := fully qualified class name, e.g. edu.kit.quickheap.QuickHeap
METHOD := METHODNAME ["(" PARAMLIST ")"]
PARAMLIST := ("I" "|" "J" "|" "[I" "|" "[J" "|" "Z" "|" "int" "|" "long" | ")"* )  // KeY type-code syntax as printed by KeY, e.g. "([I,int,int,[I)"
KIND := "JML normal_behavior operation contract"
```

Canonical examples that MUST be selectable, verbatim:
- `edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::partition([I,int,int,[I)].JML normal_behavior operation contract.0`
- `edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::randomIndex(int)].JML normal_behavior operation contract.0`

### 4.2 Selection surfaces (any one suffices to be compliant, all three preferred)

1. CLI: `--choose-contract <NAME>` (repeatable; selects the given contracts in order).
2. Load file: `\chooseContract "<NAME>";` (single contract) — same grammar as the CLI value.
3. Load file: `\proofObligation "<NAME>";` — **must accept the same NAME strings as §4.1** (currently it demands a serialized-PO file; this is the R6/E6 defect being closed).

### 4.3 Listing

`--list-contracts` prints to stdout, one contract per line, exactly:

```
<IDX>\t<FQCC>::<METHOD>\t<NAME>
```

- `<IDX>` is the ordinal that legacy `--auto` stdin selection uses (kept for compatibility).
- `<FQCC>::<METHOD>` is the "Method:" line text KeY currently prints.
- `<NAME>` is the §4.1 canonical name.
- Example first lines for the current project:
```
0	edu.kit.quickheap.QuickHeap::QuickHeap	edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::QuickHeap(long)].JML normal_behavior operation contract.0
1	edu.kit.quickheap.QuickHeap::QuickHeap	edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::QuickHeap()].JML normal_behavior operation contract.0
```
- `--list-contracts` exits `0`, prints no `KEY_RESULT` line, and must be stable across runs with identical inputs and settings (§6).

### 4.4 Errors

- Unknown value for `--choose-contract`: stderr line `KEY_ERROR contract '<NAME>' not found` plus the full listing on stdout; exit `3`.
- Ambiguous overloads: multiple entries with identical NAME → treat all of them as selected (multi-set semantics), index-qualified (`NAME.#<IDX>` also accepted as a selector).

Acceptance D1: `--list-contracts` output has as many lines as `--auto` interactive shows `Contract N:` entries, and each line's `NAME` matches the contract-name smoke-test in §9.
Acceptance D2: selecting by `--choose-contract "<NAME>"` proves the same obligation as legacy `echo <IDX>` for the same `<NAME>` row.

---

## 5. Strategy settings (reproducible)

### 5.1 Sources, precedence (high → low)

1. CLI: `--strategy-option <KEY>=<VALUE>` (repeatable).
2. CLI: `--settings-file <PATH>`.
3. Load file: `\settings { ... }` (must be accepted by the parser; currently rejected — E5).
4. KeY defaults (documented).

`--config-dir <DIR>`: makes KeY read/write ALL user-persistence from `<DIR>` instead of `~/.key`; defaults still apply inside. Runs with `--config-dir` must be byte-reproducible across hosts.

### 5.2 Settings file format (exact)

JSON object; ONLY the named keys are meaningful; a value for any key is one of the comma-form strings that appear in current proof headers. Required schema (keys in any order):

```json
{
  "intRules": "intRules:arithmeticSemanticsIgnoringOF|intRules:javaSemantics|intRules:checked|intRules:unchecked",
  "integerSimplificationRules": "integerSimplificationRules:standard|integerSimplificationRules:full|integerSimplificationRules:recursive",
  "javaLoopTreatment": "javaLoopTreatment:default|javaLoopTreatment:efficient|javaLoopTreatment:expand|-javaLoopTreatment",
  "assertions": "assertions:off|assertions:safe",
  "runtimeExceptions": "runtimeExceptions:ban|runtimeExceptions:allow",
  "bigint": "bigint:on|bigint:off",
  "programRules": "programRules:Java|programRules:JavaCard",
  "methodExpansion": "methodExpansion:modularOnly|methodExpansion:full",
  "Strings": "Strings:on|Strings:off",
  "sequences": "sequences:on|sequences:off",
  "reach": "reach:on|reach:off",
  "permissions": "permissions:on|permissions:off"
}
```

### 5.3 Failure semantics

- Unknown key or bad value → `KEY_ERROR settings: '<LINE>' not understood` (with the exact offending source line) on stderr; exit `3`; nothing proven.
- Settings must affect the run they are passed to, and **must not be persisted back** into `~/.key` (or `--config-dir`), except into files the caller explicitly requested.

Acceptance E1: `--settings-file` with the §5.2 example that sets `intRules:intRules:javaSemantics` changes the strategy manifest (visible in proof header) compared to the default, for the identical contract.
Acceptance E2: same `--settings-file` + same load file ⇒ `--list-contracts` output is byte-identical on two runs and on two machines.
Acceptance E3: `--strategy-option intRules=intRules:unchecked` on an overflow-sensitive contract changes the `openGoals` count (or closes it) compared to `intRules:check`; if not, print `KEY_WARN` (see §8) and still exit per §1.

---

## 6. Open-goal inspection

`--print-open-goals [<MAX>]` (default `MAX=10`, `MAX=0` = unlimited): prints, after proof search, the open goals on stdout, formatted exactly:

```
OPEN-GOAL-COUNT <N>
GOAL <id> <position-path>
  <antecedent-term>
  ==> <succedent-term>
<blank line>
```

- `<id>` integer ≥ 0; `<position-path>` a KeY position path string (dot-separated ints), the one usable by §7 `at <position-path>`.
- Terms rendered in KeY printer syntax; each formula on its own line (no wrapping); a line with `\n`-escapes.
- `MAX` truncates the number of GOAL blocks to `MAX`; `OPEN-GOAL-COUNT` always prints the true total.
- `--no-truncate-formulas` disables any long-formula truncation.

Acceptance F1: two runs on the same open contract ⇒ identical `OPEN-GOAL-COUNT` and identical GOAL blocks.
Acceptance F2: for the `size()` contract (currently open), each printed formula is non-empty and every `<position-path>` matches `^[1-9][0-9.]*$`.

---

## 7. Scripted proving and sound replay

### 7.1 Script file grammar (line-oriented, `#` comments, UTF-8)

```
script      := { line }
line        := cmd
cmd         := "proceed"                          // one auto-strategy step
             | "apply" rule-name [ "at" position ] [ "for" term ]
             | "auto" [ limit ]                    // run strategy up to limit steps
             | "assert-closed"
             | "print-open-goals"
```
- `position` := the `<position-path>` from §6.
- A script applies to the currently selected/loaded obligation (chosen via §4).
- Execution: lines executed in order against the *single* open goal designated by the last `GOAL` in the previous `print-open-goals`, or by `at` anchors. Result of each command line printed to stdout as `SCRIPT OK <line>` or `SCRIPT FAIL <line> <reason>`.
- At end, `assert-closed` prints `SCRIPT FINAL closed` (exit 0) or `SCRIPT FINAL open <n>` (exit 1). If the script has no `assert-closed`, outcome comes from the §2 record.

### 7.2 Replay

`--replay <PROOF> [--contract <NAME>]`:
- Loads `<PROOF>`, re-checks it against the current load file/class sources.
- Prints exactly one of:
  - `REPLAY closed 0` (exit `0`)
  - `REPLAY unclosed <n>` (exit `1`)
  - `REPLAY incompatible <reason>` (exit `3`)
- The marker rule of §3 determines "closed" if the proof has no internal status; if both exist they must agree.

Acceptance G1: a genuinely closed proof (§9, trivial) → `REPLAY closed 0`, exit 0.
Acceptance G2: putting an `KEY_PROOF_STATUS open 3` header on the same file → `REPLAY unclosed 3`, exit 1.
Acceptance G3: a hand-script (≥2 distinct commands, incl. `apply`) on the known-open `size()` obligation reports `SCRIPT OK` for every command, then `openGoals` drops strictly between first and last `print-open-goals`.

---

## 8. Diagnostic errors (JML/Java translation and runtime)

All Must-fail conditions print, on stderr, a line starting with the literal `KEY_`:

- `KEY_ERROR <file>:<line>:<col>: construct '<SNIPPET>' not supported: <REASON>` — construct/parse problems, exit `3`.
- `KEY_WARN <message>` — non-fatal, exit per §1.

Inputs that MUST produce `KEY_ERROR` (not an NPE) with `<SNIPPET>` filled:
1. `assignable bucketData[*][*];` → snippet `bucketData[*][*]`.
2. `int[][] a = new int[n][];` → snippet `new int[n][]`.
3. `int[][] a = new int[][]{{1,2}};` → snippet `new int[][]{{1,2}}`.
`<line>:<col>` = 1-based position of the construct in the source file.

Acceptance H1: a 3-file suite containing each construct → each run exits `3`, stderr has one `KEY_ERROR` line whose `<SNIPPET>` equals the listed value, and `KEY_ERROR` line count == number of bad constructs.

---

## 9. Acceptance test matrix (execute as one script)

Fixture sources (files under `/tmp/ke/index`; load file `index.key` with the two class entries):

```java
// C.java
public class C {
  /*@ public normal_behavior
    @   ensures \result == 1; @*/ public int one() { return 1; }
  /*@ public normal_behavior
    @   ensures \result == 1; @*/ public int two() { return 2; }
}
```

| # | Run | Expected exit | Expected stdout markers |
|---|---|---|---|
| 1 | `--choose-contract '<NAME one()>'` | 0 | `KEY_RESULT ... "status":"closed" ... "openGoals":0` |
| 2 | `--choose-contract '<NAME two()>'` | 1 | `"status":"open"` and `"openGoals">0` |
| 3 | `--auto --timeout=1` (same file) | 2 | `"status":"timed_out"` |
| 4 | `--choose-contract 'NoSuch'` | 3 | stderr `KEY_ERROR contract 'NoSuch' not found` |
| 5 | `--list-contracts` | 0 | ≥2 lines of form `<IDX>\t<clazz>::<m>\t<NAME>`, no `KEY_RESULT` line |
| 6 | `--settings-file s.json` citing unknown key `"foo": "x"` | 3 | stderr `KEY_ERROR settings:` |
| 7 | `--print-open-goals 5` on #2 | 1 | `OPEN-GOAL-COUNT >= 1`, ≤5 `GOAL ` blocks |
| 8 | `--replay` of the #1-produced proof | 0 | `REPLAY closed 0` |
| 9 | `--replay` of a partial saved via `--save-partial` | 1 | `REPLAY unclosed <n>` |
| 10 | bad construct suite (§8) | 3 | `KEY_ERROR ... construct '<snippet>'` |

The project's real gate (`verify/verify.sh`) adopts the §2/§3 contract as follows:

```bash
# prove one contract: honest outcome
out=$(printf '%s\n' "$idx" | java -Xmx2g -jar "$KEY_JAR" --auto --timeout="$T" "$KEYFILE")
last=$(printf '%s' "$out" | grep -a '^KEY_RESULT ' | tail -n 1)
status=$(printf '%s' "$last" | sed -n 's/.*"status":"\([^"]*\)".*/\1/p')
closed_flag=$([ "$status" = closed ] && [ -s "${PROOF:-none}" ] && echo 1 || echo 0)
```

---

## 10. Stability and documentation requirements

- §1–§9 features are documented in the official KeY docs: exact flag names, exact JSON schema, exact exit-code table.
- `--list-contracts` ordering: for identical input files, identical settings, identical binary ⇒ byte-identical output (test E2). Document at least 10 examples of JML/source changes that MAY reorder it and state that scripts must use §4.2 selection, never ordinals (§4.3 keeps ordinals only for legacy `--auto`).

## 11. Out of scope (unchanged)

GUI; proving-heuristic performance; new calculus rules; non-KeY JML tools; supporting `.proof` files not following §3.
