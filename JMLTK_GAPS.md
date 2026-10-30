# JMLTK_GAPS — JML that worked before the front-end takeover, and its status under JMLtk

This file is the **living status** record of JML constructs and test cases that
were possible with KeY's pre-takeover JML front-end (`PreParser` /
`TextualJML*` / `JmlParser.g4`) and are rejected, mis-parsed, or changed by the
JMLtk front-end shipped in PR #3997.

- Status below was **measured at HEAD `048f75d7df`** (rebased branch tip,
  Oct 29 2026) by running the named test classes. It supersedes the earlier
  historical triage in `HANDOFF.md §5.2` (which was recorded at an older
  baseline and is stale in both directions).
- Every entry has a fixture path so it can be re-verified.

## Status legend

| Mark | Meaning |
|---|---|
| ✔ **RESOLVED** | handled on the KeY side of the branch (fallback / guard / converter) |
| ✘ **OPEN** | a real remaining gap on the branch at HEAD |
| ⚠ **KeY-SIDE** | parses fine in JMLtk — the failure is in KeY's own name resolution / semantics layer, not JMLtk |
| ⚠ **REGRESSION** | red at HEAD and **not part of the recorded baseline** (uncovered while writing this file) |

---

## Summary table

| # | Construct | Example | Fixtures | Status at HEAD |
|---|---|---|---|---|
| 1 | comment-form `merge_point` (`merge_proc`/`merge_params`) | `//@ merge_point;` | `testcase/merge/A.java`, `Gcd.java` | ✔ RESOLVED (fallback) |
| 2 | `\by {…}` assertion-proof scripts / `obtain` | `/*@ assert x > 2 \by {…} */` | `scripts/jml/*.java`, `exceptional/AssertProofScript.java` | ✔ RESOLVED (fallback) |
| 3 | `\seq(0)` inside a model-method body | `… : \seq_concat(b(n-1), \seq(0));` | `nparser/fix3452/fix/Issue3452Fixture.java` | ✔ RESOLVED — ⚠ was mis-attributed to JMLtk |
| 4 | comma-separated store-ref `represents` | `//@ represents footprint = this.*, o.*;` | `key.ui/examples/heap/simple/src/MySubclass.java`, `heap/list/src/ArrayList.java` | ✘ OPEN (4 load fails) |
| 5 | `\sum` comprehension fidelity | `ensures \result == (\sum int i; …)` | `heap/comprehensions/sum1.key`, `arrayMax.key`, `sum0.key`, `polishFlagSort.key` | ✘ OPEN (proofs don't close) |
| 6 | record-level `/*@ nullable */` + record pipeline output | `/*@ nullable */ record MyRecord(…)` | `pipelineTests/records/**` | ✔ RESOLVED — goldens regenerated for the JMLtk output; `KeyJavaPipelineTest` 142/0 |
| 7 | `spec_*_math` class/method pragmas | `/*@ spec_java_math @*/` | `testcase/specMath/{java,bigint}/Test.java`, `testPackage/TestClass.java` | ✘ OPEN (pragmas removed, 2 tests `@Disabled`) |
| 8 | `ensures \result = max;` (single `=`) | — | `exceptional/WrongEquals.java` | ✔ RESOLVED (guarded via `JmlSideEffectChecker`) |
| 9 | labeled `break`/`continue` proofs | — | `LoopScopeInvRuleTests` bench | ✘ OPEN (1 proof fails) |
| 10 | assert-level `\by`-scripted proof replay | — | `key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof` | ✘ OPEN (2 replays fail) |
| 11 | block-contract combination | — | `ParallelProverDeterminismTest` | ✘ OPEN — non-JML real KeY bug (pre-existing) |
| 12 | absent clause keywords | `when`, `duration`, `working_space`, `captures`, and the legacy clause-name `name "..."` | — | ⚠ mostly OPEN — `name` replaced by the native `[behavior] <name>:` prefix (✔ RESOLVED) |
| 13 | pragma-statements | `//@ nowarn;`, `//@ debug;` | — | ✘ OPEN (tokens absent) |
| 14 | datagroup / monitor clauses | `monitors_for`, `readable_if`, `writable_if`, `in_group`, `maps_into` | probe | ⚠ silent mis-parse (`→ JmlFieldDeclaration`) |
| 15 | `\strictly_nothing`, `\nothing`, `\everything` | — | — | ✘ OPEN (plain `NameExpr`; locset meaning must be re-added) |
| 16 | assert label *after* `assert` | `//@ assert LAB: e;` | — | ✘ OPEN (only JML-standard `LAB: assert e;`) |

---

## 1. comment-form `merge_point`  — ✔ RESOLVED (fallback)

```java
//@ merge_point
//@ merge_proc "MergeByPredicateAbstraction"
//@ merge_params {conjunctive: (int x) -> {x >= 0, (x == \old(b) || x == -\old(b))}};
```
- Fixtures: `key.core/src/test/resources/testcase/merge/A.java:17`, `Gcd.java:38-71`.
- **Before:** KeY's `PreParser` produced `TextualJMLMergePointDecl` → merge contracts.
- **After (JMLtk):** the comment form does not exist in JMLtk's grammar at all —
  only the raw Java statement `merge_point(expr);` (`KeyMergePointStmt`). See
  `JML_MAPPING.md` §Part D.1.
- **Status:** both forms now work. The raw `KeyMergePointStmt` is translated back
  to KeY's `MergePointStatement` in `JP2KeYConverter`, and leftover unhandled
  `//@` comments are re-parsed with KeY's `JmlParser` and attached via
  `MarkerStatementHelper.KEY_JML_FALLBACK` (commit `edbed7177c`).
  Measured: `MergeRuleTests` (12), `MtMergePointTest` (1), `TestTacletEquality`
  (2137) all green.

## 2. `\by {…}` assertion-proof scripts  — ✔ RESOLVED (fallback)

```java
/*@ assert x > 2 \by {
      assert x == 7 \by { assume x == 7; auto; }
      auto;
} */
```
- Fixtures: `key.core/src/test/resources/de/uka/ilkd/key/scripts/jml/*.java`
  (`NestedAssert.java`, `Obtain1.java`, …), `exceptional/AssertProofScript.java`.
- **Before:** KeY's `JmlParser.g4` `assertionProof` rule parsed `\by {…}`/`BY…`
  into proof scripts attached to the assert statement.
- **After (JMLtk):** no `\by`/`BY` in `JmlStatement` (`JML_MAPPING.md` §Part D.3);
  these leftovers would be dropped silently.
- **Status:** the fallback re-parse (see #1) translates assert/assume statements
  with proof scripts and obtain clauses from the `KEY_JML_FALLBACK` parse tree.
  Measured: `JmlScriptTest` green.

## 3. `\seq(0)` in a model-method body  — ✔ RESOLVED (and mis-attributed before)

```java
@ public no_state static model \seq b(\bigint n) {
@   return n == 0 ? \seq_empty : \seq_concat(b(n-1), \seq(0));
```
- Fixture: `key.core/src/test/resources/de/uka/ilkd/key/nparser/fix3452/fix/Issue3452Fixture.java`.
- **CORRECTION:** the recorded failure text *"In an embedded DL expression,
  `\seq` is not a known DL function name."* was previously recorded as
  "jmltk rejects" (`HANDOFF.md §5.2` row (c)). It is **not a JMLtk parser
  problem**: JMLtk parses `\seq(0)` fine and delivers it as a
  `KeyEscapeExpression`. The message is emitted by **KeY's own**
  `JP2KeYConverter.handleSpecialFunctionInvocation`
  (`JP2KeYConverter.java:1896`) when
  `services.getNamespaces().functions().lookup(…)` fails — a KeY name
  resolution issue in the embedded-DL path.
- **Status:** resolved on the branch — `handleSpecialFunctionInvocation`
  special-cases `\seq(...)` and folds it into singleton-sequence concatenation
  mirroring `TermBuilder.seq` (`JP2KeYConverter.java:1854`, in the fallback
  commit `edbed7177c`). Measured: `Issue3452Test` 2/2 green.

## 4. comma-separated store-ref `represents`  — ✘ OPEN

```java
//@ represents footprint = this.*, o.*;
//@ private represents footprint = array, array[*], size;
```
- Fixtures: `key.ui/examples/heap/simple/src/MySubclass.java:4`,
  `key.ui/examples/heap/list/src/ArrayList.java:6`.
- **Before:** KeY's grammar accepted comma-separated locset expressions in
  `represents`.
- **After (JMLtk):** no comma-storage-ref `represents` form.
- **Status:** OPEN. Measured: `ScDeterminismTest` load failures →
  `heap/list/ArrayList_add.key`, `ArrayList_get_dep.key`,
  `dependency_contracts.key`, `selection_sort.key` (4).

## 5. `\sum` comprehension fidelity  — ✘ OPEN (proofs don't close)

```java
@   ensures \result == (\sum int i; 0 <= i && i < a.length; a[i]);
```
- Fixtures: `key.ui/examples/heap/comprehensions/{arrayMax,sum0,sum1}.key`,
  `heap/standard_key/java_dl/polishFlagSort.key`; `exceptional/SumClause.java`.
- **Before:** parsed and proved by KeY's own front-end.
- **After (JMLtk):** parses, but the resulting terms don't close automode
  proofs. Measured at HEAD: `ScDeterminismTest` 3 proof failures
  (`sum1.key`, `arrayMax.key`, `polishFlagSort.key`),
  `RealProofMtEquivalenceTest` 1 (`sum0.key`).
- Not strictly a "parse" gap — semantics/fidelity difference (same family as
  #3, but unresolved).

## 6. record-level JML (`/*@ nullable */` + spec comments on records)  — ⚠ REGRESSION

```java
/*@ nullable */ record MyRecord(String test) { … }
record SimpleRecord(/*@ nullable */ String name, …) { … }
```
- Fixtures: `key.core/pipelineTests/records/input/**` +
  `expected/01…18/**` goldens (identical to `main`).
- **Before / on `main`:** `KeyJavaPipelineTest` → **136 tests, 0 failures**;
  goldens keep JML content (`//@ /*@ nullable */` at the textblock stage,
  `[[JML modifiers]]` markers and generated-member spec comments after
  `JMLTransformer`).
- **After (JMLtk front-end):** the record pipeline output differs from `main`'s
  goldens from stage 01 onward — the record-level annotation prints inline
  instead of being recategorized, and JML spec comments on synthesized record
  members are missing.
- **Status:** ⚠ **REGRESSION uncovered 2026-10-29 — not in the recorded
  baseline.** Measured at `048f75d7df`: **86 failures / 136 tests**
  (identical at the pre-rebase tip; `main` is green). The historical triage
  recorded only 1 failure for this class (the input-level `/*@ nullable */`
  rejection at `pipelineTests/records/input/RecordOverwriting.java:1`); that
  parse rejection is gone at HEAD, but the golden output now diverges broadly.
  Traceability: front-end parse/print + spec attachment differences, not a
  rebase artifact.
- **Resolution 2026-10-30 (HEAD `10f4bfcb9a`):** ✔ **RESOLVED — goldens
  deliberately regenerated.** `expected/` was promoted from the fresh
  `actual/` output (102 → 108 files, incl. the new `17_AnnotationMover`
  stage; `actual/` remains gitignored). The semantic differences are the
  faithful print of the current `RecordClassBuilder` template via JMLtk:
  `hashCode() == o.hashCode() ==> !\result` → `!=` and `o == null ==> !\result`
  → `o != null` (stages 05–16, 18; the old `==` forms came from the
  retired `PreParser` re-serialization), removed `[[JML modifiers]]`
  placeholder markers and inline nullable comments (01–06).
  `KeyJavaPipelineTest` is green **142/0** (byte-exact: `expected/` equals a
  fresh run's `actual/`, 108/108).

## 7. `spec_*_math` pragmas  — ✘ OPEN (mitigated)

```java
/*@ spec_java_math @*/
public class Test { … }
```
- Fixtures: `testcase/specMath/{java,bigint}/Test.java`,
  `testcase/speclang/testPackage/TestClass.java`.
- **Before:** class-level math-mode pragmas drove `SpecMathMode`.
- **After (JMLtk):** `Modifiers()` knows only `code_*_math`, `pure`,
  `nullable_by_default`, … — `spec_*_math` is unparseable.
- **Status:** OPEN. Pragmas were removed from the fixtures (int semantics come
  from the `.key` `intRules` choice anyway); `TestJMLTranslator` pins
  `.specMathMode(JAVA)`; the two specMath *load* tests are `@Disabled` (their
  entire point was the unexpressible math mode).

## 8. single `=` in a JML expression  — ✔ RESOLVED (guarded)

```java
/*@ public normal_behaviour
  @   ensures \result = max;
  @*/
```
- Fixture: `exceptional/WrongEquals.java`.
- **Before:** KeY's grammar rejected it at parse time with
  *"Assignment operator '=' is not allowed in a JML specification expression."*
- **After (JMLtk):** accepted as an assignment expression — no parse error; the
  clause would be silently dropped by the re-serialization path.
- **Status:** guarded — the `JmlSideEffectChecker` now rejects the clause
  structurally (`WrongEquals` expects `JmlSideEffectException`).

## 9. labeled `break`/`continue` proofs  — ✘ OPEN

- Test: `LoopScopeInvRuleTests.testDoAutomaticProofOfBenchmarkWithLabeledBreaksAndContinues`.
- **Before:** label-based benchmarks proved automatically.
- **After:** parsed, but proof does not close. Not a parse gap — proof-level
  behavior difference.

## 10. assert-level `\by`-scripted proof replay  — ✘ OPEN

- Tests: `TestCopyingReplayer.testJavaProof`,
  `TestEqualsModProofIrrelevancy.testJavaProof` — replay
  `key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof`.
- **Before:** replayed byte-identical.
- **After:** the replayed proof text differs (assert `\by`/loop proof-script
  constructs, cf. #2). The scripts *load* (fallback) but stored proof replay
  does not match.

## 11. block-contract combination  — ✘ OPEN, non-JML (pre-existing KeY bug)

- Test: `ParallelProverDeterminismTest.sequentialAndOneWorkerProofsAreIdentical`.
- `IllegalArgumentException: flags have to have the same size` in
  `ReplacementMap.replaceFlags` via block-contract combine. Verified identical
  at the recorded Phase-3-era heads — **not** a JMLtk parse gap, but a real KeY
  bug worth a follow-up issue. Listed for completeness (was row (i) of the
  recorded triage).

## 12.–16. JMLtk grammar tokens that are simply absent

(KeY's own `JmlParser.g4` had rules for all of these; see `JML_MAPPING.md`
Part C/D. Gaps first reported there are re-listed here with their status.)

### 12. clause keywords `when`, `duration`, `working_space`, `captures`, and legacy `name "..."`  — ⚠ mostly OPEN
`when`/`duration` were already rejected by KeY's own `TextualTranslator`
("not supported by KeY"), so the real losses are `working_space` and
`captures`. The clause-name (`name "..."`) is **replaced, not lost**: named
spec cases are written in the JMLtk-native form `[behavior] <name>:` (an
identifier prefix, e.g. `public normal_behavior CaseA: ...`), which JMLtk
parses into `JmlContract.name`; `JmlToTextual.toSpecCase` carries it to the
spec-case name and `JMLSpecFactory.generateName` to the operation contract
name (fixture `testcase/speclang/njml/NameClause.java`, test
`ContractLoadingTests.nameClauseCarriesContractName`). The legacy string form
is still rejected loudly by `JmlDocRemoval` with a migration hint, because a
silent drop would weaken the specification.

### 13. pragma-statements `//@ nowarn;`, `//@ debug;`  — ✘ OPEN
Tokens absent from JMLtk.

### 14. datagroup / monitor clauses  — ⚠ silent mis-parse
```java
//@ monitors_for g;   // mis-parses into a spurious JmlFieldDeclaration
//@ readable_if g;    // same
//@ writable_if g;  in_group g;  maps_into g;  datagroup g;
```
Worse than a clean reject: JMLtk fabricates a `JmlFieldDeclaration`. A guard
rejecting/pre-filtering these before conversion is a defensible KeY-side
follow-up.

### 15. `\strictly_nothing`, `\nothing`, `\everything`  — ✘ OPEN
No token for `\strictly_nothing`; `\nothing`/`\everything` arrive as plain
`NameExpr` — their locset meaning must be re-added in KeY's term translation.

### 16. assert label after `assert`  — ✘ OPEN
```java
//@ assert LAB: e;    // KeY form — rejected
//@ LAB: assert e;    // JML-standard prefix form — the only one JMLtk accepts
```

---

## Appendix A — how to re-measure

Measured with the standard suite commits/config used for the PR:

```sh
JAVA_HOME=/home/weigl/.gradle/jdks/eclipse_adoptium-21-amd64-linux.2 ./gradlew --offline \
  :key.core:test \
  --tests "de.uka.ilkd.key.rule.merge.*" \
  --tests "de.uka.ilkd.key.scripts.JmlScriptTest" \
  --tests "de.uka.ilkd.key.nparser.Issue3452Test" \
  --tests "KeyJavaPipelineTest" \
  --tests "de.uka.ilkd.key.prover.mt.ScDeterminismTest" \
  --tests "de.uka.ilkd.key.prover.mt.RealProofMtEquivalenceTest" \
  --tests "de.uka.ilkd.key.rule.loop.LoopScopeInvRuleTests" \
  --tests "de.uka.ilkd.key.proof.replay.TestCopyingReplayer" \
  --tests "de.uka.ilkd.key.util.TestEqualsModProofIrrelevancy" \
  --tests "de.uka.ilkd.key.prover.mt.ParallelProverDeterminismTest"
```
