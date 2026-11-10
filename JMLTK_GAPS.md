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
- 2026-11-08 CI-integration + RunAll-corpus triage (branch tip `4b62b1d6fa`;
  `testRunAll*` jobs are CI-only, so the per-proof triage was done with a
  **local** corpus run at the branch tip):
  - `testMt*` / `testRunAllWdProofs` — §18 (quicksort ghost locals, load
    failure, present at 1.1.0 **and** 1.2.1); Wd is now green.
  - `testRunAllFunProofs` (22 red groups) / `testRunAllInfProofs` (10–11 red
    groups) — **all PR-induced** (`origin/main`'s Tests workflow is fully
    green, incl. both RunAll jobs). New gaps recorded here: §17 upgraded to a
    **save→reload blocker** (RunAll `other`, `list_seq`), §19
    (`ensures_redundantly`, group `SmansEtAl`), §20 (`assignable_free`,
    group `javadl`), §21 (committed `perm.proof` replay drift, group
    `reload_examples`); the rest are §4 (comma `represents` → load failure:
    Fun `list`, `javaCard`, `funOfIF`, `simple_info_flow`, `simpleTests`; Inf
    `NewObjects`), §18 (Fun `quicksort`), §5 (`\sum` fidelity: Fun
    `comprehensions`), or proofs that simply no longer close under the new
    front-end (spec/sequent-shape drift — Fun `newBook`, `blockContracts`,
    `list_ghost`, `observer`, `example-algos`, `VACID0`, `VSTTE10`,
    `FM2024Tutorial`, `WeideEtAl`, `redux`; Inf `ToyVoting{,_fullmacro}`,
    `ConditionalConfidential`, `SumExample{,_nomacro,_fullmacro}`,
    `ToyBanking{,_fullmacro}`, `SimpleEvoting{,_fullmacro}`).
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
| 1 | comment-form `merge_point` — legacy `merge_proc`/`merge_params` **and** JMLtk 1.2.1 `\by`/`\lattice`/`\predicate` | `//@ merge_point \by "…" \lattice conjunctive \predicate (int x) : …;` | `testcase/merge/{A,Gcd}.java`, `testcase/merge/newsyntax/MergeNewSyntax.java` | ✔ RESOLVED (legacy → leftover fallback; 1.2.1 syntax → typed `JmlMergePointStmt`, `53dcefd914`, covered by `MergePointJmltkSyntaxTest`) |
| 2 | `\by {…}` assertion-proof scripts / `obtain` | `/*@ assert x > 2 \by {…} */` | `scripts/jml/*.java`, `exceptional/AssertProofScript.java` | ✔ RESOLVED (fallback) |
| 3 | `\seq(0)` inside a model-method body | `… : \seq_concat(b(n-1), \seq(0));` | `nparser/fix3452/fix/Issue3452Fixture.java` | ✔ RESOLVED — ⚠ was mis-attributed to JMLtk |
| 4 | comma-separated store-ref `represents` | `//@ represents footprint = this.*, o.*;` → `//@ represents footprint = \locset(this.*, o.*);` | 10 example files, 11 sites (`heap/{simple,list,javacard,information_flow,vacid0_05_RedBlackTrees}`, `InformationFlow/PasswordFile`) | ✔ RESOLVED by syntax adoption (2026-11-09); load failures cleared, residual drift recorded below |
| 5 | `\sum` comprehension fidelity | `ensures \result == (\sum int i; …)` | `comprehensions/{sum0,sum1}.key` | ✔ RESOLVED (2026-11-11: sum0/sum1 close again, `\bsum` term byte-identical to `origin/main`; restored by the jmltk `1.2.1-SNAPSHOT` line — see §5) |
| 6 | record-level `/*@ nullable */` + record pipeline output | `/*@ nullable */ record MyRecord(…)` | `pipelineTests/records/**` | ✔ RESOLVED — goldens regenerated for the JMLtk output; `KeyJavaPipelineTest` 142/0 |
| 7 | `spec_*_math` class/method pragmas | `/*@ spec_java_math @*/` | `testcase/specMath/{java,bigint}/Test.java`, `testPackage/TestClass.java` | ✔ RESOLVED (JML modifiers → `SpecMathMode`; `SpecMathModeTest` 2 + `ContractLoadingTests` 6 green) |
| 8 | `ensures \result = max;` (single `=`) | — | `exceptional/WrongEquals.java` | ✔ RESOLVED (guarded via `JmlSideEffectChecker`) |
| 9 | labeled `break`/`continue` proofs | — | `LoopScopeInvRuleTests` bench | ✔ RESOLVED (loop-invariant fix `6a07c20e63`) |
| 10 | `relax.proof` scripted-proof replay | — | `key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof` | ✔ RESOLVED (2026-11-10: loop invariant lost in `elim_double_block_3` rebuild; fixed via `#reattachLoopInvariant` — see §10) |
| 11 | block-contract combination | — | `ParallelProverDeterminismTest` | ✘ OPEN — non-JML real KeY bug (pre-existing) |
| 12 | absent clause keywords | `when`, `duration`, `working_space`, `captures`, and the legacy clause-name `name "..."` | — | ⚠ mostly OPEN — `name` replaced by the native `[behavior] <name>:` prefix (✔ RESOLVED) |
| 13 | pragma-statements | `//@ nowarn;`, `//@ debug;` | `exceptional/NowarnDebug.java`, `exceptional/NowarnDebugInMethod.java` | ⚠ pinned: class level loud (`ProofInputException`), method level dropped (fallback) |
| 14 | datagroup / monitor clauses | `monitors_for`, `readable_if`, `writable_if`, `in_group`, `maps_into` | `exceptional/{Datagroup,MonitorsFor,ReadableIf,WritableIf,InGroup,MapsInto}.java` | ✔ RESOLVED (loud guard, no spurious fields) |
| 15 | `\strictly_nothing`, `\nothing`, `\everything` | — | `LocsetClauseTranslationTest` | ✔ RESOLVED (measured 2026-11-10: names re-lex to the special tokens; residual: method-level `accessible` is a JMLtk-upstream gap, fallback mitigates) |
| 16 | assert label *after* `assert` | `//@ assert LAB: e;` | — | ✘ OPEN (only JML-standard `LAB: assert e;`) |
| 17 | origin-label file info for re-parsed JML | `Precondition @ [no file]` | any JMLtk-converted spec (assert/assume/set, contract clauses, fallback) | ✘ OPEN (**save→reload blocker** — `[no file]` origins are not re-parseable; RunAll `other`, `list_seq`) |
| 18 | DL-typed ghost locals with initializer | `//@ ghost \seq x = \dl_array2seq(a);` | `key.ui/examples/heap/quicksort/{sort,split}{,-jmlscript}.key` | ✘ OPEN (load failure — JMLtk reads `ghost` as field-level; pre-existing at 1.1.0 **and** 1.2.1) |
| 19 | `ensures_redundantly` clause kind | `@ ensures_redundantly e;` | `key.ui/examples/heap/SmansEtAl/src/Iterator.java:11` | ✘ OPEN (load failure — JMLtk accepts it, KeY `JmlParser.g4` has no production) |
| 20 | `assignable_free` clause body | `@ assignable_free \nothing;` / `@ assignable_free field;` | `key.ui/examples/standard_key/java_dl/jml-free/{AssignableFree,AssignableLoopFree}.java` | ✘ OPEN (load failure — `UnsolvedSymbolException` on the clause keyword) |
| 21 | committed `.proof` replay drift | `heap/permutedSum/perm.proof` | the tracked proof (155 tracked `.proof` files total; this one fails) | ✘ OPEN (replay errors: rule position no longer fits, built-in reconstruction fails) |

---

## 1. comment-form `merge_point`  — ✔ RESOLVED (fallback)

```java
//@ merge_point
//@ merge_proc "MergeByPredicateAbstraction"
//@ merge_params {conjunctive: (int x) -> {x >= 0, (x == \old(b) || x == -\old(b))}};
```
- Fixtures: `key.core/src/test/resources/testcase/merge/A.java:17`,
  `Gcd.java:38-71` (legacy form); `testcase/merge/newsyntax/MergeNewSyntax.java`
  (JMLtk 1.2.1 form).
- **Before:** KeY's `PreParser` produced `TextualJMLMergePointDecl` → merge contracts.
- **After (JMLtk 1.1.0):** the comment form does not exist in JMLtk's grammar at
  all — only the raw Java statement `merge_point(expr);` (`KeyMergePointStmt`).
  See `JML_MAPPING.md` §Part D.1.
- **Status (1.1.0):** both forms work. The raw `KeyMergePointStmt` is translated
  back to KeY's `MergePointStatement` in `JP2KeYConverter`, and leftover
  unhandled `//@` comments are re-parsed with KeY's `JmlParser` and attached via
  `MarkerStatementHelper.KEY_JML_FALLBACK` (commit `251f945131`).
  Measured (Appendix A at `8fe1be5b6c`): `MergeRuleTests` (12) and
  `PredicateAbstractionLatticeTests` (3) green; `MtMergePointTest` (1) and
  `TestTacletEquality` (2137) were green at the original measurement.
- **JMLtk 1.2.1 (commit `53dcefd914`) — typed node, *different syntax*:**
  JMLtk now parses a comment-form merge point into a *typed*
  `JmlMergePointStmt` (`com.github.javaparser.ast.jml.stmt`, new in 1.2.1) —
  but the syntax is **not** the legacy KeY `merge_proc`/`merge_params` form.
  The 1.2.1 JML grammar (javacc `JmlMergePoint()`) accepts only:

  ```java
  //@ merge_point;
  //@ merge_point \by MergeByIfThenElse;                       // string literal or plain identifier
  //@ merge_point \by "MergeByPredicateAbstraction" \lattice conjunctive
  //         \predicate (int x) : x >= 0, x == \old(b) || x == -\old(b);
  ```

  i.e. `merge_point` followed by the options `\by <name>`, `\lattice <name>`
  and `\predicate (T v) : p1, p2, …`, each optional and in exactly that order;
  `\by`/`\lattice` values may be a string literal or a plain identifier
  (normalized to `StringLiteralExpr`). The node exposes `by`, `lattice`,
  `predicateVariable`, `predicates`. **The legacy multi-line
  `//@ merge_point` + `//@ merge_proc "…"` + `//@ merge_params {…};` form is
  *not* parsed by JMLtk** (JMLtk's own `FullExamplesTest` rewrites KeY's
  `firstTouch/11-StateMerging/Gcd.java` from it to the new form); it remains an
  unparsed leftover handled by the `KEY_JML_FALLBACK` re-parse. So at HEAD both
  comment forms work through different paths:
  - *new 1.2.1 syntax* → typed `JmlMergePointStmt` →
    `JP2KeYConverter.visit(JmlMergePointStmt)` (temp boolean location var) +
    `JMLSpecFactory#createJMLMergeContracts(JmlMergePointStmt)`, which
    re-serializes the node's `by`/`lattice`/`predicateVariable`/`predicates`
    to the **textual legacy form** `merge_point merge_proc "X" merge_params
    {L: (T v) -> {p1, p2}};` and re-parses it with KeY's `JmlParser`
    (`merge_point_statement`), reusing the shared translation.
  - *legacy syntax* → leftover `JmlDocStmt` → `KEY_JML_FALLBACK` re-parse →
    `createJMLMergeContracts(Merge_point_statementContext)`.
  A bare `merge_point;` (no options) is parsed typed in both versions.
- **Measured at HEAD:** `MergeRuleTests` (12) and
  `PredicateAbstractionLatticeTests` (3) green (legacy form, via fallback);
  `MergePointJmltkSyntaxTest` (3, new at `HEAD`) loads
  `testcase/merge/newsyntax/merge.newsyntax.{bare,byId,param}.key` and asserts
  the typed path end to end: bare → default `MergeByIfThenElse` contract,
  `\by MergeByFullAnonymization` → `MergeTotalWeakening` contract, full form →
  `PredicateAbstractionMergeContract` with lattice `conjunctive` and 2
  abstraction predicates. Note: contract extraction runs for *every* method of
  a loaded class, so an unknown procedure name in *any* method aborts every
  load of that class (`Unknown merge procedure: "…"`).

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

## 4. comma-separated store-ref `represents`  — ✔ RESOLVED by syntax adoption (2026-11-09)

```java
//@ represents footprint = this.*, o.*;              // legacy KeY form (pre-takeover)
//@ represents footprint = \locset(this.*, o.*);     // JMLtk grammar
```
- Fixtures: `key.ui/examples/heap/simple/src/MySubclass.java:4`,
  `key.ui/examples/heap/list/src/ArrayList.java:6`.
- **Before:** KeY's grammar accepted comma-separated locset expressions in
  `represents`.
- **After (JMLtk):** no comma-separated store-ref `represents` form. JMLtk's JML
  grammar hits a hard problem (`Encountered unexpected token: ","`) on the first
  comma of the locset list, so the whole Java source fails to load. JMLtk's
  grammar instead models the store-set as `\locset(…)` — lexed as an identifier
  (the `LOCSET` token is not a JML keyword in JMLtk), i.e. a method call whose
  arguments are the store-refs; valid in `represents` **and** `set` statements.
- **Resolution (2026-11-09, user-directed adoption):** all affected example
  sources rewritten to the `\locset(…)` form — 11 sites in 10 files:
  `heap/simple/src/MySubclass.java`, `heap/list/src/{ArrayList,LinkedList,MySet}.java`,
  `heap/javacard/src/javacard/framework/{CardRuntimeException,OwnerPIN}.java`
  (OwnerPIN: 2 sites, incl. the multi-line `footprint` clause),
  `heap/information_flow/src/ArrayList.java`,
  `heap/vacid0_05_RedBlackTrees/src/vacid0/redblacktree/{Node,RedBlackTree}.java`
  (not in any CI corpus), `InformationFlow/PasswordFile/src/passwordfile/SecurePasswordFile.java`
  (nested `\locset(\locset(names, passwords), names[*], passwords[*])` — the
  mechanical wrap of the legacy list, term-identical to the old form).
  No test resources or READMEs used the legacy form.
- **Verification (scratch parse against the 1.2.1-SNAPSHOT in use):** JMLtk
  parses every rewritten form (incl. the exotic javacard arguments
  `_pin[0]`, `_pin.\transient`, `\transactionUpdated(_pin)`,
  `\reachLocs(first.next, first)`), `JmlToTextual.toRepresents` re-serializes it
  and KeY's own `JmlParser.g4` re-parses it (`represents_clause` →
  `primaryStoreRef` → `storeRefUnion`); the resulting term is **identical** to
  the legacy comma form (e.g. `MySubclass::footprint ==
  union(allFields(self), allFields(o))`), so no spec change. The old comma form
  is confirmed rejected by the same parser (`Encountered unexpected token: ","`).
- **Measured (2026-11-09 local corpus run at `20d361fa85`):** the 4
  `ScDeterminismTest` load failures cleared (`heap/list/ArrayList_add.key`,
  `heap/list/ArrayList_get_dep.key`, `heap/simple/dependency_contracts.key`,
  `heap/simple/selection_sort.key` now load — the first three close and are
  single-core reproducible). RunAll Fun **22 → 20 red groups**:
  - `funOfIF` (8/8) and `simple_info_flow` (2/2 notprovable) now **pass** —
    no drift in these groups.
  - `simpleTests`: 27/28 pass; only `selection_sort.key` doesn't close.
  - `list`: 25/29 pass; doesn't close: `ArrayList_concatenate`,
    `ArrayList_contains_dep`, `ArrayList_enlarge`, `LinkedList_get_normal`.
  - `javaCard`: 2/5 pass; doesn't close: `setArray1`, `setArray2`,
    `arrayFillNonAtomic` (all load; `updateBalance0/1` close).
  The §4 parse failure is gone from the corpus; the new doesn't-close proofs
  above are the front-end's spec/sequent-shape drift, same family as the
  pre-existing 11 drift groups (per-proof debugging pending — see
  `TODO_CI.md` §4).
  - **Residual detail for `selection_sort`:** A/B against `origin/main`
    (same file + same strategy closes there; the `MySubclass::footprint`
    represents axiom is term-identical on both sides, so the rewrite is not
    the cause). Open goal is the outer-loop exit obligation; its
    loop-invariant terms carry `<<origin(… ([loop_invariant @ [no file]]))>>`
    (cf. §17).
  - ~~`heap/comprehensions/sum1.key` remains a doesn't-close failure (gap
    §5).~~ — closes again as of 2026-11-11 (gap §5 re-measured RESOLVED).

## 5. `\sum` comprehension fidelity  — ✔ RESOLVED (re-measured 2026-11-11)

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
  #3, but resolved).
- **Resolution 2026-11-11 (re-measured at tip `cfece36950`, local jmltk
  `1.2.1-SNAPSHOT` jar of 2026-11-07):** the `\bsum` fidelity is restored —
  no branch code change was needed. Verified three ways:
  - The two named gates are green in a fresh run: `ScDeterminismTest` 14/0
    (`sum1.key` closes in both runs, bit-identical) and
    `RealProofMtEquivalenceTest` 8/0 (`sum0.key` closes single-threaded and
    multi-threaded).
  - Term-level A/B against `origin/main`: the initial goal sequents of
    `sum0.key`/`sum1.key` carry the byte-identical `\bsum` term
    `bsum{i:int}(Z(0(#)), length(a), select<int>(heap,a,arr(i)))`; the only
    difference between the front-ends is the §17 `ensures @ [no file]` origin
    label.
  - The whole Fun `comprehensions` RunAll group matches its expectations: all
    10 `provable` fixtures close, `bsumSplitInvalid.key` stays open.
  No branch commit between the red measurement (`53dcefd914`, CI 2026-11-08)
  and the green re-measurement touches the JML-to-term path, so the fidelity
  improvement comes from the jmltk `1.2.1-SNAPSHOT` line itself (CI fetches
  the snapshot at build time; the exact fixing snapshot is unpinned).
  Caveat: `1.2.1-SNAPSHOT` is moving — re-verify on the next snapshot bump /
  release pin.

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

## 10. `relax.proof` scripted-proof replay  — ✔ RESOLVED (2026-11-10)

- Tests: `TestCopyingReplayer.testJavaProof`,
  `TestEqualsModProofIrrelevancy.testJavaProof` (key.core), and
  `TestReferenceSearcher#testFindsReferenceInSameProof` (keyext.caching) — all
  load `key.ui/examples/heap/verifyThis15_1_RelaxedPrefix/relax.proof`.
- **Before:** replayed byte-identical.
- **After (pre-fix):** the load-time replay tracked the stored script
  node-for-node, then the **"Loop Invariant" rule** (`WhileInvariantRule`) at
  the loop-head goal aborted with `RuleAbortException("no invariant found")`;
  the step and its whole subtree were skipped and the proof loaded **not
  closed** (open node 40, 43 nodes vs. 4048 on `origin/main`).
- **Root cause (measured 2026-11-10 — supersedes the earlier `\strictly_nothing`
  frame attribution, which is wrong):** the goal program's `While` carried no
  attached `LoopSpecification` because the preceding
  `elim_double_block_3` step **rebuilds the `While` node** from the taclet
  pattern (`{ while(e) S }` → `while(e) S`) and the node-attached invariant was
  not carried over. Walked the replayed left spine with a scratch dump:
  - node 24 (after `methodBodyExpand`): `For plainInv=set` — PO init +
    `ProgVarReplaceVisitor` param substitution copy the invariant ✓
  - node 35 (after `for_to_while`): `While plainInv=set` —
    `ForToWhileTransformation` copies it ✓
  - nodes 35–39 (`i=0;` execution, OSS, `elim_double_block`): `While id=X
    plainInv=set` ✓
  - node 40 (result of `elim_double_block_3`): **`While id=Y
    plainInv=null`** ✗ — a fresh node, invariant lost.
  On `origin/main` the same reconstruction still resolves the invariant,
  because `SpecificationRepository.loopInvs` is keyed by
  `Pair<LoopStatement, Integer>` with **structural** `equals`/`hashCode`
  (`JavaProgramElement` hash = class + children; `LoopStatement.equals` = same
  class + position UNDEFINED or same line): the rebuilt While (UNDEFINED
  position) matches the registration of the original. The branch's
  node-attached design has no such fallback —
  `LoopInvariantBuiltInRuleApp.retrieveLoopInvariantFromSpecification` is a
  plain `loop.getLoopInvariant()` on the fresh node.
- **Fix:** re-attach the invariant in the reconstructing taclet, the same way
  `unwindLoopScope` already does: `elim_double_block_3`'s replacement now uses
  `#reattachLoopInvariant(while ( #e ) #s);` (the matched loop is the active
  statement, so `ReattachLoopInvariant` finds it in the match context and
  re-attaches it to the rebuilt node; no-op when no invariant is attached).
  `ReattachLoopInvariant` was generalized from `While` to `LoopStatement`
  (forward-compatible). The `for`/`do` variants (`elim_double_block_4..8`)
  have the same latent loss but are **not** extended yet: the JMLtk grammar
  (pinned `1.2.1-SNAPSHOT`) only accepts a `while` argument to
  `#reattachLoopInvariant`, so that needs a JMLtk grammar extension first
  (follow-up with the jmltk release pin).
- **Result (measured at the fix commit):** replay of `relax.proof`
  `closed=true nodes=4049`; `TestCopyingReplayer`, `TestEqualsModProofIrrelevancy`
  and `TestReferenceSearcher` all green. The `TestTacletEquality` golden
  (`key.core/src/test/resources/de/uka/ilkd/key/nparser/taclets.old.txt`) was updated
  for the new `elim_double_block_3` rendering (2137/2137 green).
- **Related (same commit):** `AnnotationMover` logged
  `ERROR "unexpected class: …JmlQuantifiedExpr"` for every JML bound variable
  (JMLtk parents the `VariableDeclarator` of a `\forall` under
  `JmlQuantifiedExpr`) — 116 errors per `relax.proof` load; the `Jmlish`
  parent is now skipped silently.

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

### 15. `\strictly_nothing`, `\nothing`, `\everything`  — ✔ RESOLVED (measured 2026-11-10)
**Stale — the names work.** JMLtk lexes all three locset names as
`JML_IDENTIFIER` into a `NameExpr` **that keeps the leading backslash**;
`JmlToTextual.exprList` re-serializes them verbatim, and KeY's own `JmlLexer`
(expr mode) re-lexes them to the special tokens `STRICTLY_NOTHING` (211),
`NOTHING` (179) and `EVERYTHING` (133). The parse then takes the
`storeRefUnion → storeRefList → storeref` production (not the assignable-clause
`STRICTLY_NOTHING` alternative) and the `Translator` maps them to
`tb.strictlyNothing()` / `tb.empty()` / `tb.createdLocs()` respectively —
identical to the pre-takeover translation. Measured in every clause position
(`assignable`, `modifies`, `represents`, loop contracts); pinned by
`LocsetClauseTranslationTest` (5 tests).

Residual (upstream, mitigated): JMLtk has **no method-level `accessible`
clause** — its `JmlClassAccessible` production requires the class-level
`accessible <var> : <exprs>;` form, so the KeY method-level forms
(`accessible this.x;`, `accessible \nothing;`) are a hard JMLtk error. The
`KEY_JML_FALLBACK` re-parse with KeY's own grammar recovers them, so the
status quo is: class-level `accessible` is JMLtk-native (via
`JmlToTextual.toDepends`), method-level `accessible` goes through the
fallback. Tracked as a JMLtk-upstream grammar gap, not a branch defect.

### 16. assert label after `assert`  — ✘ OPEN
```java
//@ assert LAB: e;    // KeY form — rejected
//@ LAB: assert e;    // JML-standard prefix form — the only one JMLtk accepts
```

## 17. `[no file]` in origin term labels  — ✘ OPEN (save→reload blocker, display otherwise cosmetic)

- **Symptom (display):** origin labels on JML terms re-parsed from the JMLtk AST render
  as e.g. `Precondition @ [no file]` instead of the pre-takeover
  `Precondition @ file Foo.java @ line 42`.
- **Symptom (reload — found 2026-11-08 in the RunAll triage):** a proof
  **saved** under the JMLtk front-end contains origin strings like
  `requires @ [no file]`; reloading that proof **fails**, because
  `OriginTermLabelFactory.parseOrigin` accepts only `(implicit)`,
  `@ file <name> @ line <n>` and `@ node <n> (<rule>)` — it throws
  `TermLabelException("Malformed origin string: \"requires @ [no file]\"")`
  on the `[no file]` form that `FileOrigin.toString()` itself renders for
  null-URI origins (`OriginTermLabel.java:743`). The renderer and the parser
  are asymmetric.
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
- **Impact:**
  - *Display:* cosmetic — `OriginTermLabel.isProofRelevant()` is `false` and
    replay compares via `EqualityModuloProofIrrelevancy`.
  - *Save→reload (NEW, 2026-11-08):* **blocker**. The RunAll corpus saves
    proofs and reloads them in the same run (reload-enabled groups); the
    saved file carries `requires @ [no file]` origins and the reload aborts
    with the `Malformed origin string` above. Measured (local run at branch
    tip, Fun corpus): group `other`
    (`heap/verifyThis26_01_hIndex/update.key.proof`, saved proof line 4806)
    and group `list_seq`
    (`heap/list_seq/SimplifiedLinkedList.remove.key.proof`, line 1575).
    Any saved proof that contains a JMLtk-converted spec (contract clauses
    included — the failing origins are `requires` clauses of operation
    contracts) fails to reload; this is a branch-side round-trip bug, not a
    defect of the recorded recordings.
- **Fix options:** (a) propagate the JMLtk node's position to the re-parse
  (URI via `CompilationUnit.getStorage().getPath()` + line/column) so origins
  carry a real file — fixes display *and* round-trip; (b) make
  `parseOrigin` accept the `[no file]` rendering (map it to a null-URI
  `FileOrigin`); (c) render null-URI origins as `(implicit)`.
  Documented but not fixed at `53dcefd914`.

## 18. DL-typed ghost locals with initializer (quicksort)  — ✘ OPEN (load failure, pre-existing)

```java
//@ ghost \seq seq3 = \dl_array2seq(array);
```
- Fixtures: `key.ui/examples/heap/quicksort/{sort,sort-jmlscript,split,split-jmlscript}.key`
  (all load `Quicksort.java`).
- **Symptom:** the proof fails to **load** (`ProblemLoaderException` ←
  `BuildingExceptions`) — it is never proved or replayed.
- **Root cause (JMLtk parse dump, `53dcefd914`):** JMLtk (both
  `1.1.0-SNAPSHOT` and `1.2.1-SNAPSHOT`) parses the KeY-specific ghost *local*
  `//@ ghost \seq <name> = \dl_array2seq(array);` as a class-level
  `JmlFieldDeclaration` (`ghost` is a field-level modifier in standard JML)
  and reports the hard problem *"Class-level JML declaration
  JmlFieldDeclaration is not allowed within methods"*. `JavaService.unwrapParseResult`
  only tolerates the method-level "Could not handle the JML comment" gap (plus
  the accompanying location-less ANTLR problems), so this hard problem aborts
  the load. (A plain `//@ ghost T x = plainCall();` without the DL-escape
  initializer does parse as `JmlGhostStmt`.)
- **Also in the file (tolerated, not fatal):** two `\by` proof scripts with
  KeY-specific commands (`oss;`, `rule "…";`, `case "…":`,
  `instantiate hide:true …`) → JMLtk "Could not handle the JML comment" →
  leftover handled by the `KEY_JML_FALLBACK` re-parse.
- **Pre-existing, not from the bump:** CI 2026-11-02 at `ed348636cb` (jmltk
  `1.1.0-SNAPSHOT`) failed identically (`MtScriptStressTest` ×2, same exception
  at the same line). Unrecorded until now because the `testMt*`/`testRunAll*`
  integration jobs were not part of the local Appendix-A baseline.
- **CI impact:** `testMtStress` (`MtScriptStressTest` ×2) and the `quicksort`
  group of `testRunAllFunProofs`.
- **Fix options:** fix upstream in JMLtk (a `ghost` local with a DL
  type/initializer must parse as a statement, not a class-level field); or
  rewrite the example source; or (KeY-side) tolerate this specific hard problem
  and convert the statement-position `JmlFieldDeclaration` back into a ghost
  local — conflicts with the loud-failure policy and needs care.

---

## 19. `ensures_redundantly` clause kind  — ✘ OPEN (load failure, JMLtk accepts, KeY grammar lacks it)

```java
@ ensures_redundantly l.footprint == \old(l.footprint);
```
- Fixture: `key.ui/examples/heap/SmansEtAl/src/Iterator.java:11`.
- **Symptom:** loading any `.key` file in the `SmansEtAl` group fails —
  whole-group load failure in `testRunAllFunProofs` (group `SmansEtAl`).
- **Root cause:** `ensures_redundantly` is a standard-JML clause; JMLtk
  parses it into a typed clause of kind `ENSURES_REDUNDANTLY`. KeY's
  `JmlParser.g4` (the grammar `JmlToTextual` re-serializes against) has
  **no production** for this clause kind (0 occurrences), so
  `JmlToTextual`'s kind dispatch falls through to
  `throw new …("Unsupported clause kind: ENSURES_REDUNDANTLY " + clause)`
  (`JmlToTextual.java:348/382`). Before the takeover the same source parsed
  with KeY's old JML front-end (which tolerated/ignored the clause); the
  re-serialization design exposes the missing production as a hard error.
- **CI impact:** `testRunAllFunProofs` group `SmansEtAl` (Fun corpus red on
  the branch, green on `main` — PR-induced).
- **Fix options:** add an `ensures_redundantly` production to `JmlParser.g4`
  and translate it like `ensures` (the "redundantly" modifier is a
  soundness hint, not extra semantics — verify against the JML reference
  before dropping the qualifier); or reject the clause kind explicitly with
  a targeted message.

## 20. `assignable_free` clause body  — ✘ OPEN (load failure, symbol resolution)

```java
@ assignable_free \nothing;
@ assignable_free field;
```
- Fixtures: `key.ui/examples/standard_key/java_dl/jml-free/AssignableLoopFree.java:14,22`
  (and `AssignableFree.java` in the same directory); group = the 13 `.key`
  files of `key.ui/examples/standard_key/java_dl/jml-free/`.
- **Symptom:** load fails with
  `UnsolvedSymbolException{context='null', name='assignable_free'}` thrown
  from `JP2KeYConverter`'s `ClassOrInterfaceType` handling
  (`getKeYJavaType` → `type.resolve()`, `JP2KeYConverter.java:1268`, via
  `visit(ClassOrInterfaceType)` at `:449`).
- **Root cause:** JMLtk parses the KeY-specific `assignable_free <expr>`
  clause and exposes the clause keyword position as a Java type node in the
  AST; the converter runs the javaparser symbol resolver on it, which
  cannot resolve `assignable_free` (it is a clause keyword, not a type).
  KeY's own re-parse path for `assignable_free` exists (`JMLSpecFactory`
  re-parses `assignable_free \nothing;` with `JmlFacade.parseClause`), so
  the clause is expressible in `JmlParser.g4` — the crash happens before
  that path, during Java-AST conversion.
- **CI impact:** `testRunAllFunProofs` group `javadl` (whole group).
- **Fix options:** in the converter, do not symbol-resolve clause-keyword
  positions (skip resolution for JML clause nodes), or convert the
  `assignable_free` clause via its typed JML node before the generic
  type-visitor reaches it.

## 21. committed `perm.proof` no longer replays  — ✘ OPEN (replay drift)

- Fixture: `key.ui/examples/heap/permutedSum/perm.proof` (tracked; 1 of the
  155 tracked `.proof` files under `key.ui/examples`), group
  `reload_examples` (`TestProperty.LOADABLE`).
- **Symptom:** the proof **loads** (environment-level load succeeds) but the
  recorded replay reports **6 errors** → `replayResult.hasErrors()` → group
  fails. Error mix (reproduced locally at branch tip):
  - `IntermediateProofReplayer$TacletAppConstructionException: Could not
    reconstruct the rule application: the stored position does not fit the
    current sequent` (a `Perm::#pIdx`-heavy goal), and
  - `BuiltInConstructionException: One Step Simplification is missing …`
    (the replayer finds no reconstructable application for the stored
    built-in step — the generic "missing binary" wording of
    `IntermediateProofReplayer.java:735` for a not-reconstructable app).
- **Interpretation:** the proof was recorded with the pre-takeover front-end;
  under the JMLtk front-end the spec/sequent shape at some goals differs
  enough that recorded rule applications no longer reconstruct. Same family
  as the `relax.proof` replay gap (§10) — a committed proof whose recording
  is stale against the new front-end. Not a save/reload format bug: a plain
  `KeYEnvironment.load` of the file succeeds.
- **CI impact:** `testRunAllFunProofs` group `reload_examples`.
- **Fix options:** regenerate the recording under the JMLtk front-end
  (re-prove `perm.key` and re-record), or repair the drift at its source
  (whichever of the §4/§5/§17/§18-style shape differences feeds these goals).

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
