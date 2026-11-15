# KeY Headless Command-Line Interface

This is the official documentation of the headless (script/agent-friendly) command-line
interface of KeY. It covers the exact flag names, the machine-readable result protocol, the
exit-code contract, and the diagnostic formats that scripts and LLM agents can implement
against with zero ambiguity. The normative source is
[`docs/superpowers/specs/2026-11-14-key-cli-interface-spec.md`](superpowers/specs/2026-11-14-key-cli-interface-spec.md).

The interface is implemented by the `key.cli` module, entry point
`org.key_project.key.cli.Main`. Run the subcommands of

```
key-cli [options] <subcommand> [arguments]
```

where the subcommands are `prove`, `list`, `script`, and `replay`. The spec's flat
invocation style (`--auto …`, `--list-contracts`, …) is mapped onto this subcommand layout
(one flag per concern instead of a single mega-command); the legacy
`( echo <IDX> | java -jar key.jar --auto … )` invocation keeps working unchanged.

## 1. Exit codes

| Code | Meaning | Printed result status |
|---|---|---|
| `0` | one or more contracts proven, **all** closed | `closed` |
| `1` | at least one selected contract not closed (goal remains) | `open` |
| `2` | proof search abandoned by timeout (no decision — not "open") | `timed_out` |
| `3` | input error (file not found, parse error, unknown option, unknown contract, bad settings) | `error` |
| `4` | internal error (exception not attributable to input) | `error` |

The exit code reflects the **worst** status among the selected contracts (one `closed` plus
one `open` ⇒ exit `1`). A failed *load* of an input file is an input error (exit `3`) unless
the cause chain indicates an internal bug (e.g. a `NullPointerException`), in which case the
exit is `4`.

## 2. Result record (`KEY_RESULT`)

In any proving subcommand, one line per proven contract is written to **stdout**, and the
`KEY_RESULT` lines are the **last N lines** of stdout (no other line of stdout may start with
the prefix). The line is the literal 11-character prefix `KEY_RESULT ` followed by a single
JSON object, terminated by `\n`:

```
KEY_RESULT {"version":1,"contract":"edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::partition([I,int,int,[I)].JML normal_behavior operation contract.0","status":"closed","openGoals":0,"elapsedMs":1234,"proofFile":null,"smtCalls":0,"smtProved":0,"errorMessage":null}
```

| field | type | semantics |
|---|---|---|
| `version` | int | protocol version, currently `1` |
| `contract` | string | canonical contract name actually proven (see §4.1) |
| `status` | string | `"closed"`, `"open"`, `"timed_out"`, or `"error"` |
| `openGoals` | int | number of open goals at termination; `0` iff `status=="closed"` |
| `elapsedMs` | int | wall-clock milliseconds of proof search for this contract |
| `proofFile` | string \| null | absolute path of the written proof file, or `null` (see §3) |
| `smtCalls` | int | SMT solver invocations (0 unless an SMT rule is enabled) |
| `smtProved` | int | goals proved via SMT (0 unless an SMT rule is enabled) |
| `errorMessage` | string \| null | human-readable message; non-null iff `status=="error"` |

Listing (`list`) prints no `KEY_RESULT` line. For a file that cannot be loaded, one `error`
record is printed whose `contract` field names the failed input file and whose
`errorMessage` carries the load-failure message (including the structured construct
diagnostic of §8).

## 3. Proof files

- **Default**: no `.proof` file is written anywhere unless requested via `--proof` or
  `--proof-dir`.
- `--proof <PATH>`: writes the proof of the (single selected) contract to `PATH`.
- `--save-partial`: an unclosed proof is then also saved to the requested location.
- Every written proof file starts with a status marker line:

  ```
  KEY_PROOF_STATUS closed 0
  ```

  for a closed proof, or

  ```
  KEY_PROOF_STATUS open <openGoals>
  ```

  for a saved unclosed proof (`<openGoals>` ≥ 1). Consumers: read the first line; it equals
  `KEY_PROOF_STATUS closed 0` iff the proof is closed.
- No proof file is written to a location the caller did not request via `--proof` /
  `--proof-dir` (in particular, no surprise `<file>.auto.N.proof` files).

## 4. Contract selection and listing

### 4.1 The contract name grammar

A contract name is a single line (no newlines) matching

```
NAME := CLASS "[" METHOD "]" "." KIND ["." INT]
CLASS := fully qualified class name, e.g. edu.kit.quickheap.QuickHeap
METHOD := METHODNAME ["(" PARAMLIST ")"]
PARAMLIST := KeY type-code syntax as printed by KeY, e.g. "([I,int,int,[I)"
KIND := "JML normal_behavior operation contract"
```

Canonical examples that must be selectable verbatim:

- `edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::partition([I,int,int,[I)].JML normal_behavior operation contract.0`
- `edu.kit.quickheap.QuickHeap[edu.kit.quickheap.QuickHeap::randomIndex(int)].JML normal_behavior operation contract.0`

### 4.2 Selection surfaces

1. **CLI**: `--choose-contract <SELECTOR>` (repeatable, `prove` and `script`). A selector is
   a bare index (the ordinal printed by `list`), `NAME.#<IDX>`, or an exact canonical name
   (all contracts sharing the name are selected — multi-set semantics for ambiguous
   overloads). Selection order is command-line order.
2. **Load file**: `\chooseContract "<NAME>";` — same NAME grammar as the CLI value.
3. **Load file**: `\proofObligation "<NAME>";` — accepts the same NAME strings as §4.1.

Without any selector, the load file's `\chooseContract`/`\proofObligation` directive selects
the contract; without a directive, all contracts are proven.

### 4.3 Listing

`list <files>` prints to stdout, one contract per line, exactly

```
<IDX>\t<FQCC>::<METHOD>\t<NAME>
```

- `<IDX>` — the ordinal (kept for legacy `--auto` stdin selection compatibility).
- `<FQCC>::<METHOD>` — the "Method:" line text KeY prints, e.g. `C::one`.
- `<NAME>` — the §4.1 canonical name.

```
0	C::one	C[C::one()].JML normal_behavior operation contract.0
1	C::two	C[C::two()].JML normal_behavior operation contract.0
```

`list` exits `0`, prints no `KEY_RESULT` line, and is stable across runs with identical
inputs and settings (see §9).

### 4.4 Errors

Selecting an unknown contract prints, on stderr,

```
KEY_ERROR contract '<NAME>' not found
```

plus the full listing on stdout, and exits `3`.

## 5. Strategy settings

### 5.1 Sources and precedence (high → low)

1. CLI: `--strategy-option <KEY>=<VALUE>` (repeatable).
2. CLI: `--settings-file <PATH>`.
3. Load file: `\settings { … }`.
4. KeY defaults.

For the same key, a `--strategy-option` overrides the `--settings-file` entry, which
overrides the load-file `\settings` block. Settings are applied **only for the duration of
the run** and are never persisted back into `~/.key` (or `--config-dir`), except into files
the caller explicitly requested.

`--config-dir <DIR>` (root option, also accepted as `--config-dir=<DIR>`, scanned from any
position of the command line): makes KeY read and write **all** user persistence from
`<DIR>` instead of `~/.key`. Defaults still apply inside. Runs with `--config-dir` are
byte-reproducible across hosts and leave the real `~/.key` untouched.

### 5.2 Settings file format

`--settings-file <PATH>` takes a flat JSON object whose keys are, in any order, **only**:

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

Each value is one of the comma-form strings shown (the `key:category` strings that appear in
KeY proof headers). `--strategy-option <KEY>=<VALUE>` uses the same vocabulary.

### 5.3 Failure semantics

An unknown key or undocumented value is an input error:

```
KEY_ERROR settings: '<LINE>' not understood
```

(`'<LINE>'` is the exact offending source line or `key=value` pair), exit `3`, nothing
proven.

## 6. Open-goal inspection

`prove --print-open-goals [<MAX>]` (default `MAX=10`; `MAX=0` = unlimited) prints, after
proof search and before the `KEY_RESULT` line, the open goals on stdout:

```
OPEN-GOAL-COUNT <N>
GOAL <id> <position-path>
  <antecedent-term>
  ==> <succedent-term>

```

- `<id>` is an integer ≥ 0; `<position-path>` is the dot-separated int KeY position path
  (matching `^[1-9][0-9.]*$`), usable by the §7.1 `at <position-path>` anchor.
- `OPEN-GOAL-COUNT` always prints the **true** total; `MAX` only bounds the number of
  printed `GOAL` blocks.
- Each formula is printed on its own line (embedded line breaks escaped as literal `\n`).
  By default a formula longer than 200 characters is truncated with a `...` marker;
  `--no-truncate-formulas` disables the truncation.
- Output is deterministic across runs with identical inputs and settings.

## 7. Scripted proving and replay

### 7.1 `script` subcommand

```
key-cli script <load-file> <script-file> [--choose-contract <SELECTOR>] [--timeout <MS>]
```

The script file is line-oriented UTF-8; lines starting with `#` (and blank lines) are
ignored. The script applies to the single obligation selected via §4.2 (the selection must
resolve to exactly one contract). Grammar:

```
script      := { line }
cmd         := "proceed"                          // one auto-strategy step
              | "apply" rule-name [ "at" position ] [ "for" term ]
              | "auto" [ limit ]                    // run strategy up to limit steps
              | "assert-closed"
              | "print-open-goals"
```

Each executed line is acknowledged on stdout as

```
SCRIPT OK <line>
```

or, on failure,

```
SCRIPT FAIL <line> <reason>
```

At the end, `assert-closed` prints `SCRIPT FINAL closed` (exit `0`) or
`SCRIPT FINAL open <n>` (exit `1`); without `assert-closed`, the outcome comes from the
`KEY_RESULT` record (exit per §1).

### 7.2 `replay` subcommand

```
key-cli replay <proof-file> [--contract <NAME>]
```

Loads `<proof-file>`, re-checks it against the current load file and class sources, and
prints exactly one of:

```
REPLAY closed 0          (exit 0)
REPLAY unclosed <n>      (exit 1)
REPLAY incompatible <reason>   (exit 3)
```

The §3 marker line determines "closed" if the proof carries no internal status; if both
exist, they must agree.

## 8. Diagnostics

All must-fail conditions print, on stderr, a line starting with the literal `KEY_`:

- `KEY_ERROR <file>:<line>:<col>: construct '<SNIPPET>' not supported: <REASON>` —
  a JML/Java construct that KeY's translation does not support (e.g.
  `assignable bucketData[*][*];`, `new int[n][]`, `new int[][]{{1,2}}`).
  `<line>:<col>` is the **1-based** position of the construct in the source file,
  `'<SNIPPET>'` is the exact source text of the construct. Exit `3`. This replaces the
  former `NullPointerException`/`ClassCastException` crashes; the same structured message
  is also carried in the `errorMessage` of the `error` result record.
- `KEY_ERROR contract '<NAME>' not found` — unknown `--choose-contract` selector (exit `3`).
- `KEY_ERROR settings: '<LINE>' not understood` — unknown settings key or undocumented
  value (exit `3`).
- `KEY_ERROR file not found: <PATH>` — missing input or settings file (exit `3`).
- `KEY_ERROR <usage message>` — unknown option, missing argument, … (exit `3`).
- `KEY_ERROR internal error: <message>` — an unexpected exception (exit `4`).
- `KEY_WARN <message>` — non-fatal warning; the exit code follows §1.

## 9. Determinism and stability

- **Byte-identical output**: for identical input files, identical settings, and the
  identical binary, `list` (and `--print-open-goals` output) is byte-identical across runs
  and across hosts. The contract index is sorted by canonical contract name, and
  `--config-dir`/temp-home isolation removes any dependence on local state.
- **Ordinals are not stable identifiers**: `<IDX>` in the listing may move between versions
  of the *same* interface whenever the set of canonical names changes. At least the
  following JML/source changes MAY reorder or change the listing:
  1. adding a new method with a contract (a new name is inserted at its sorted position);
  2. removing a method (its name disappears and all later ordinals shift);
  3. adding a new overload (a new name with a different parameter list);
  4. renaming a method (the name changes, so its sorted position changes);
  5. changing a method's parameter types (the PARAMLIST part of the name changes);
  6. adding a behavior case (a second `normal_behavior`/`exceptional_behavior`, i.e. a
     `.1` name appears);
  7. removing a behavior case (a name disappears);
  8. adding an `exceptional_behavior` or other clause kind (new `KIND` names appear);
  9. renaming a class or moving it to another package (the CLASS part of every name of the
     class changes);
  10. adding a class (or a contract-bearing class to the load file) or removing one;
  11. changing inheritance: a class newly extends/implements a contract-bearing type, or
     stops doing so (inherited/auxiliary contracts appear or disappear);
  12. adding loop specifications (`loop_invariant`, `loop_variant`, …) to a method that had
     none (auxiliary contracts appear);
  13. attaching a first JML specification to a previously unspecced method (its contract
     appears); removing the last one (its contract disappears);
  14. adding or removing auxiliary contracts generated by the specification language
     (e.g. field invariants, `@ invariant` clauses on a new field).
- **Rule for scripts**: select contracts by §4.2 NAME (or `NAME.#<IDX>` for an ambiguous
  overload), **never by ordinal**. The `<IDX>` column is kept only for the legacy `--auto`
  stdin selection; any script that indexes the listing positionally is fragile by design.

## 10. Reference: all flags

| Command | Flag | Meaning |
|---|---|---|
| `key-cli` | `--config-dir <DIR>` | base directory for all KeY user-persistence (default `~/.key`) |
| `prove` | `<files>` (1+) | KeY problem files (`.key`) or Java sources |
| `prove` | `--timeout <MS>` | per-contract proof-search timeout, `0` = none (default) |
| `prove` | `--choose-contract <SELECTOR>` | select contracts, repeatable (bare index, `NAME.#<IDX>`, or NAME) |
| `prove` | `--settings-file <PATH>` | §5.2 settings file |
| `prove` | `--strategy-option <KEY>=<VALUE>` | single strategy choice, repeatable, overrides the settings file |
| `prove` | `--print-open-goals [<MAX>]` | print open goals after search (`MAX` default `10`, `0` = unlimited) |
| `prove` | `--no-truncate-formulas` | disable long-formula truncation in the goal printout |
| `prove` | `--proof <PATH>` | write the proof of the single selected contract to `PATH` |
| `prove` | `--proof-dir <DIR>` | for multi-contract runs, write the proofs into `DIR` as `<contract-index>.proof` |
| `prove` | `--save-partial` | also save an unclosed proof to the requested location |
| `list` | `<files>` (1+) | print the §4.3 listing, exit `0`, no `KEY_RESULT` |
| `script` | `<load-file> <script-file>` | run the §7.1 script against one obligation |
| `script` | `--choose-contract <SELECTOR>` | the single obligation (selection must resolve to exactly one contract) |
| `script` | `--timeout <MS>` | per-command proof-search timeout, `0` = none (default) |
| `replay` | `<proof-file>` | re-check the §3 proof file |
| `replay` | `--contract <NAME>` | restrict the re-check to one contract |
| all | `--help` | usage text |
