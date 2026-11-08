# JMLTK_GAPS — JML that worked before the front-end takeover, and its status under JMLtk

This file is the **living status** record of JML constructs and test cases that
were possible with KeY's pre-takeover JML front-end (`PreParser` /
`TextualJML*` / `JmlParser.g4`) and are rejected, mis-parsed, or changed by the
JMLtk front-end shipped in PR #3997.

- Status below was **measured at HEAD `53dcefd914`** (branch tip,
  Nov 8 2026, jmltk `1.2.1-SNAPSHOT`) by running the named test classes
  (Appendix A). It supersedes the earlier historical triage in
  `HANDOFF.md §5.2` (which was recorded at an older baseline and is stale in
  both directions).
- Re-measured at `53dcefd914`: the loop-invariant structural-lookup fix
  (`6a07c20e63`) resolved 3 previously-recorded reds — §9 (labeled
  break/continue) and 2 of the §5 `\sum` "proof doesn't close" cases
  (`arrayMax.key`, `polishFlagSort.key`, both loop proofs — mis-attributed to
  `\sum` fidelity). key.core red count is now **11** (was 14). See the
  per-section status for the re-measured state.
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
| 1 | comment-form `merge_point` (`merge_proc`/`merge_params`) | `//@ merge_point;` | `testcase/merge/A.java`, `Gcd.java` | ✔ RESOLVED (fallback; 1.2.1 typed `JmlMergePointStmt` handled at `53dcefd914`) |
| 2 | `\by {…}` assertion-proof scripts / `obtain` | `/*@ assert x > 2 \by {…} */` | `scripts/jml/*.java`, `exceptional/AssertProofScript.java` | ✔ RESOLVED (fallback) |
| 3 | `\seq(0)` inside a model-method body | `… : \seq_concat(b(n-1), \seq(0));` | `nparser/fix3452/fix/Issue3452Fixture.java` | ✔ RESOLVED — ⚠ was mis-attributed to JMLtk |
| 4 | comma-separated store-ref `represents` | `//@ represents footprint = this.*, o.*;` | `key.ui/examples/heap/simple/src/MySubclass.java`, `heap/list/src/ArrayList.java` | ✘ OPEN (4 load fails) |
| 5 | `\sum` comprehension fidelity | `ensures \result == (\sum int i; …)` | `comprehensions/{sum0,sum1}.key` | ✘ OPEN (sum0/sum1 don't close; `arrayMax`/`polishFlagSort` were loop-invariant, resolved by `6a07c20e63`) |
| 6 | record-level `/*@ nullable */` + record pipeline output | `/*@ nullable */ record MyRecord(…)` | `pipelineTests/records/**` | ✔ RESOLVED — goldens regenerated for the JMLtk output; `KeyJavaPipelineTest` 142/0 |
| 7 | `spec_*_math` class/method pragmas | `/*@ spec_java_math @*/` | `testcase/specMath/{java,bigint}/Test.java`, `testPackage/TestClass.java` | ✔ RESOLVED (JML modifiers → `SpecMathMode`; `SpecMathModeTest` 2 + `ContractLoadingTests` 6 green) |
| 8 | `ensures \result = max;` (single `=`) | — | `exceptional/WrongEquals.java` | ✔ RESOLVED (guarded via `JmlSideEffectChecker`) |
| 9 | labeled `break`/`continue` proofs | — | `LoopScopeInvRuleTests` bench | ✔ RESOLVED (loop-invariant fix `6a07c20e63`) |
| 10 | `relax.proof` scripted-proof replay | — | `key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof` | ✘ OPEN (2 key.core replays + keyext.caching `TestReferenceSearcher`) |
| 11 | block-contract combination | — | `ParallelProverDeterminismTest` | ✘ OPEN — non-JML real KeY bug (pre-existing) |
| 12 | absent clause keywords | `when`, `duration`, `working_space`, `captures`, and the legacy clause-name `name "..."` | — | ⚠ mostly OPEN — `name` replaced by the native `[behavior] <name>:` prefix (✔ RESOLVED) |
| 13 | pragma-statements | `//@ nowarn;`, `//@ debug;` | `exceptional/NowarnDebug.java`, `exceptional/NowarnDebugInMethod.java` | ⚠ pinned: class level loud (`ProofInputException`), method level dropped (fallback) |
| 14 | datagroup / monitor clauses | `monitors_for`, `readable_if`, `writable_if`, `in_group`, `maps_into` | `exceptional/{Datagroup,MonitorsFor,ReadableIf,WritableIf,InGroup,MapsInto}.java` | ✔ RESOLVED (loud guard, no spurious fields) |
| 15 | `\strictly_nothing`, `\nothing`, `\everything` | — | — | ✘ OPEN (plain `NameExpr`; locset meaning must be re-added) |
| 16 | assert label *after* `assert` | `//@ assert LAB: e;` | — | ✘ OPEN (only JML-standard `LAB: assert e;`) |
| 17 | origin-label file info for re-parsed JML | `Precondition @ [no file]` | any JMLtk-converted spec (assert/assume/set, fallback clauses) | ✘ OPEN (cosmetic only — labels are proof-irrelevant) |

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
  `MarkerStatementHelper.KEY_JML_FALLBACK` (commit `251f945131`).
  Measured (Appendix A at `8fe1be5b6c`): `MergeRuleTests` (12) and
  `PredicateAbstractionLatticeTests` (3) green; `MtMergePointTest` (1) and
  `TestTacletEquality` (2137) were green at the original measurement.
- **JMLtk 1.2.1 (commit `53dcefd914`):** the comment form is now parsed by
  JMLtk into a *typed* `JmlMergePointStmt` (`com.github.javaparser.ast.jml.stmt`,
  new in 1.2.1) instead of remaining an unparsed leftover — so the fallback path
  no longer sees it. The converter now has a `visit(JmlMergePointStmt)` (temp
  boolean location var, like the fallback) and the merge *contract* is re-derived
  by re-serializing the node's `merge_proc`/`merge_params` metadata to the
  textual `merge_point` statement (`JMLSpecFactory#createJMLMergeContracts`).
  Measured at `53dcefd914`: `MergeRuleTests` (12) and
  `PredicateAbstractionLatticeTests` (3) green.

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
  Measured: `JmlScriptTest` (7) green.

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
  commit `251f945131`). Measured: `Issue3452Test` 2/2 green.

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
  `heap/list/ArrayList_add.key`, `heap/list/ArrayList_get_dep.key`,
  `heap/simple/dependency_contracts.key`, `heap/simple/selection_sort.key` (4).

## 5. `\sum` comprehension fidelity  — ✘ OPEN (sum0/sum1 don't close)

```java
@   ensures \result == (\sum int i; 0 <= i && i < a.length; a[i]);
```
- Fixtures: `key.ui/examples/heap/comprehensions/{sum0,sum1}.key`;
  `exceptional/SumClause.java`.
- **Before:** parsed and proved by KeY's own front-end.
- **After (JMLtk):** parses, but the resulting terms don't close automode
  proofs. Measured at `53dcefd914`: `ScDeterminismTest` 1 proof failure
  (`sum1.key`), `RealProofMtEquivalenceTest` 1 (`sum0.key`).
- **CORRECTION (re-measured at `53dcefd914`):** `arrayMax.key` and
  `polishFlagSort.key` (previously listed here) are **not** `\sum`-fidelity
  failures — they are loop proofs whose `loop_invariant` was lost to the
  fresh-substituted-loop regression, now resolved by the structural-lookup
  fix (`6a07c20e63`). They close again and are removed from this gap.
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
  baseline.** Measured at `bf7048ca5d`: **86 failures / 136 tests**
  (identical at the pre-rebase tip; `main` is green). The historical triage
  recorded only 1 failure for this class (the input-level `/*@ nullable */`
  rejection at `pipelineTests/records/input/RecordOverwriting.java:1`); that
  parse rejection is gone at HEAD, but the golden output now diverges broadly.
  Traceability: front-end parse/print + spec attachment differences, not a
  rebase artifact.
- **Resolution 2026-10-30 (HEAD `841b999eee`):** ✔ **RESOLVED — goldens
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

## 7. `spec_*_math` pragmas  — ✔ RESOLVED (JML modifiers → `SpecMathMode`)

```java
/*@ spec_java_math @*/
public class Test { … }
```
- Fixtures: `testcase/specMath/{java,bigint}/Test.java`,
  `testcase/speclang/testPackage/TestClass.java`.
- **Before:** class-level math-mode pragmas drove `SpecMathMode`.
- **After (JMLtk):** JMLtk parses the pragmas as JML modifiers; there is no
  `SpecMathMode`-specific clause or keyword.
- **Status:** RESOLVED at `242e6eb44d` (remediation R4) — the modifier keys map
  via `ModifierKind.JML_SPEC_*` to the type's `SpecMathMode` (`JMLInfoExtractor`),
  for class, method-level and inline model-method modes. The fixtures keep their
  `/*@ spec_java_math @*/` / `/*@ spec_bigint_math @*/` pragmas. Measured at
  `8fe1be5b6c`: `SpecMathModeTest` (2) and `ContractLoadingTests` (6, incl.
  `specMathJavaMathTest`/`specMathBigintMathTest`) all green.

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

## 9. labeled `break`/`continue` proofs  — ✔ RESOLVED (`6a07c20e63`)

- Test: `LoopScopeInvRuleTests.testDoAutomaticProofOfBenchmarkWithLabeledBreaksAndContinues`.
- **Before:** label-based benchmarks proved automatically.
- **After (at `8fe1be5b6c`):** parsed, but proof did not close.
- **Root cause (re-measured at `53dcefd914`):** not a parse gap and not a
  break/continue-specific difference — the benchmark's loop invariant was lost
  to the fresh-substituted-loop regression (the `loopScopeInvDia` family binds a
  structurally-equal, position-UNDEFINED loop on which the node-attached
  invariant is null). The structural-lookup fix (`6a07c20e63`) restores it.
  Measured at `53dcefd914`: `LoopScopeInvRuleTests` green.

## 10. `relax.proof` scripted-proof replay  — ✘ OPEN

- Tests: `TestCopyingReplayer.testJavaProof`,
  `TestEqualsModProofIrrelevancy.testJavaProof` (key.core), and
  `TestReferenceSearcher#testFindsReferenceInSameProof` (keyext.caching) — all
  load `key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof`.
- **Before:** replayed byte-identical.
- **After:** the loaded proof does not match the stored (closed) proof.
  Re-measured at `53dcefd914`: the replay reports "Proof replayed
  successfully" but leaves **node 40 open** — the `Null Reference (_pat = null)`
  case whose postcondition frame derives from `assignable \strictly_nothing`
  (cf. gap #15). The source `Relaxed.java` has a `maintaining`/`decreasing` loop
  and `assignable \strictly_nothing` (no `\by` scripts, no model methods/JML
  fields), so the mismatch is the loop + `\strictly_nothing` frame, not the
  `\by`-script attribution recorded at `8fe1be5b6c`. `TestReferenceSearcher`
  fails at `assertTrue(p.closed())` (line 83) because that open goal survives
  the prune + close-by-reference.

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

### 13. pragma-statements `//@ nowarn;`, `//@ debug;`  — ⚠ pinned (level-dependent)
Tokens absent from JMLtk. At class level the unparseable comment surfaces loudly as a
`ProofInputException` ("Encountered unexpected token"); at method level the leftover falls back to
KeY's own grammar (`nowarn_pragma`/`debug_statement`) and unparseable leftovers are dropped
silently. Status quo pinned by `exceptional/NowarnDebug.java` (class, loud) and
`exceptional/NowarnDebugInMethod.java` (method, drop).

### 14. datagroup / monitor clauses  — ✔ RESOLVED (loud guard)
```java
//@ monitors_for g;   // mis-parses into a spurious JmlFieldDeclaration
//@ readable_if g;    // same
//@ writable_if g;  in_group g;  maps_into g;  datagroup g;
```
JMLtk fabricates a `JmlFieldDeclaration` (keyword as bogus type). The `JMLTransformer` guard
(`DATAGROUP_FAMILY`: `datagroup`, `in_group`, `maps_into`, `monitors_for`, `readable_if`,
`writable_if`, `mapped_by`, `repr`) rejects them loudly with an `IllegalArgumentException` instead
of installing spurious fields; pinned per keyword by
`exceptional/{Datagroup,MonitorsFor,ReadableIf,WritableIf,InGroup,MapsInto}.java`.

### 15. `\strictly_nothing`, `\nothing`, `\everything`  — ✘ OPEN
No token for `\strictly_nothing`; `\nothing`/`\everything` arrive as plain
`NameExpr` — their locset meaning must be re-added in KeY's term translation.

### 16. assert label after `assert`  — ✘ OPEN
```java
//@ assert LAB: e;    // KeY form — rejected
//@ LAB: assert e;    // JML-standard prefix form — the only one JMLtk accepts
```

## 17. `[no file]` in origin term labels  — ✘ OPEN (cosmetic only)

- **Symptom:** origin labels on JML terms re-parsed from the JMLtk AST render
  as e.g. `Precondition @ [no file]` instead of the pre-takeover
  `Precondition @ file Foo.java @ line 42`.
- **Mechanism:** the converter re-serializes clause text from the typed JMLtk
  AST and re-parses it with `JmlFacade.createLexer(String)`, whose
  `CharStreams.fromString` carries **no URI** (the `createLexer(PositionedString)`
  overload does carry URI + line/column, but the re-parse sites —
  `JP2KeYConverter.visit(JmlExpressionStmt)`, `toProofScript`, the
  `JmlDocStmt` fallback, `JMLTransformer`'s fallback re-parse — use the
  no-URI variant). `LabeledParserRuleContext.constructTermLabel` then reads
  `SourceNames.getURIFromTokenSource(...)` → null and builds
  `OriginTermLabel.FileOrigin(specType, null, line)`; `OriginTermLabel` renders
  the null-URI case as `specType + " @ [no file]"`.
- **Impact:** cosmetic only. `OriginTermLabel.isProofRelevant()` is `false` and
  replay compares via `EqualityModuloProofIrrelevancy`, so this causes no red
  job (recorded or otherwise). Fixable by re-parsing from the JMLtk node's
  position (URI via `CompilationUnit.getStorage().getPath()`), documented but
  not fixed at `53dcefd914`.

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
