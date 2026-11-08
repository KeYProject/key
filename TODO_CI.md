# PR #3997 — CI red: failing tests & root-cause hunt

Head under CI: `ed348636cb` (Tests run 2026-11-02 22:39, jmltk `1.1.0-SNAPSHOT` as published that day).
Main is green; the PR is `BEHIND` main (#4019, #4022, #4023 not yet included).

## 1. key.core — 14 failures (all match the recorded `JMLTK_GAPS.md` baseline → expected red)

| Test | Recorded reason (JMLTK_GAPS.md) |
|---|---|
| `ScDeterminismTest#singleCoreProofIsReproducible` ×7 ([6]–[10],[12],[14]) | comma-separated store-ref `represents` + `\sum`-proof fidelity |
| `RealProofMtEquivalenceTest[3]` | same family (`sum0`) |
| `LoopScopeInvRuleTests#testDoAutomaticProofOfBenchmarkWithLabeledBreaksAndContinues` | labeled `break`/`continue` proofs |
| `ParallelProverDeterminismTest#sequentialAndOneWorkerProofsAreIdentical` | pre-existing block-contract combination bug ("flags have to have the same size") |
| `TestCopyingReplayer#testJavaProof`, `TestEqualsModProofIrrelevancy#testJavaProof` | the 2 recorded replayer failures |
| `JMLParserExceptionTest` ×2 (`MethodInMethod`, `ModelFieldinMethod`) | known: JMLtk rejects `model` decl in method body; KeY expects legacy message. A/B-verified pre-existing under 1.1.0- **and** 1.2.1-SNAPSHOT |

- [ ] Action: none beyond the PR's gap triage (documented OPEN gaps)

## 2. keyext.slicing — 5 failures — ✔ FIXED (2026-11-08, commit `233ec1d9b0` + `6a07c20e63`)

All 5 were **stored-proof replay failures**: the JMLtk front-end produced a
KeY program/spec that drifted from the pre-takeover front-end, so saved
proofs (recorded with the old front-end) no longer matched at replay time.

Root causes (A/B-dumped against `origin/main` at `/tmp/key-main-check`):
1. **Loop invariants** (`6a07c20e63`): `loopScopeInvDia` & co. bind a *fresh*
   structurally-equal `LoopStatement` (position UNDEFINED) via
   `\storeStmtIn`; the node-attached invariant was null on the fresh node.
   Fix: structural reverse-lookup in `LoopStatement.getLoopInvariant(program)`.
2. **Model-method contracts** (`233ec1d9b0`): JMLtk attaches the contract to
   the inner `MethodDeclaration`, not the `JmlMethodDeclaration` wrapper; the
   extractor only read the wrapper → trivial `true` contract → missing
   `Contract_axiom_for_gcd_in_ParallelGcd` taclet. Fix: collect from both.
3. **Model-method bodies** (`233ec1d9b0`): the JML definition was built as an
   executable Java body (`\old` → "not a known DL function name"). Fix:
   signature-only conversion when a JML wrapper is present (mirrors
   `TextualJMLMethodDecl.getParsableDeclaration`).
4. **JML field initializers** (`233ec1d9b0`): JMLtk kept `//@ ghost ... = null`
   initializers on unwrapped fields → inlined into `Throwable.$init` →
   `methodCallEmpty` body mismatch. Fix: strip initializers in
   `JMLTransformer` (the old front-end materialized JML fields bare).

Verified: `:keyext.slicing:test` **17/17 green** (all 5 previously-red tests
pass; the 6 `ReplayErrorDumpTest` scratch dumps were deleted, 23 → 17).

## 3. keyext.caching — 2 failures — 1 FIXED, 1 accounted (recorded gap §10)

- [x] `ProofCachingSingleRunTest#cachingClosesInASingleRun` — **FIXED** by the
  loop-invariant fix (`6a07c20e63`). `BinarySearch_search.key` proves a
  `loop_invariant`+`decreases` loop; the fresh-node invariant regression left the
  auto run unable to close. Now green.
- [x] `TestReferenceSearcher#testFindsReferenceInSameProof` — **ACCOUNTED**: it
  loads `relax.proof`, the SAME recorded OPEN gap as §10 / JMLTK_GAPS §10 (the two
  key.core replayer tests). Confirmed by scratch dump: the replay reports
  "Proof replayed successfully" but leaves node 40 open (the `Null Reference
  (_pat = null)` case whose postcondition frame derives from
  `assignable \strictly_nothing`, cf. gap #15). Fails at `assertTrue(p.closed())`
  (line 83). Not one of the four program-shape drifts (the source has a
  `maintaining`/`decreasing` loop + `\strictly_nothing`; no model methods / JML
  fields / `\by` scripts).

## 4. Integration jobs (ubuntu) — red — triaged at `4b62b1d6fa` (CI run 2026-11-08)

- [x] `testRunAllWdProofs` — **now PASSING** (red at 2026-11-02) — resolved by the
  program/spec-shape fixes (`6a07c20e63` + `233ec1d9b0`).
- [x] `testMt2w` / `testMt4w` — **ACCOUNTED**: the curated small-MT collections
  (`ProofCollections.smallMultiThreaded{,Splitting}`) contain exactly the
  recorded failing proofs — `selection_sort`, `dependency_contracts`,
  `ArrayList_get_dep`, `ArrayList_add` (JMLTK_GAPS §4 store-ref load fails) and
  `sum1` (§5). The `multithreaded_smoke`/`multithreaded_splitting` group
  failures are those recorded gaps surfacing through the MT runner; the
  `ScDeterminismTest` ×5 in the same job is the identical set. No new MT
  prover failure.
- [x] `testMtStress` — `MtScriptStressTest` ×2 = **newly identified,
  pre-existing, previously unrecorded gap** (JMLTK_GAPS §18):
  `heap/quicksort/sort.key` fails to **load** — JMLtk (1.1.0 **and** 1.2.1)
  parses the `//@ ghost \seq x = \dl_array2seq(array);` ghost locals as
  class-level `JmlFieldDeclaration` → hard parse problem. Same failure in the
  2026-11-02 CI (1.1.0) — not caused by the 1.2.1 bump.
- [ ] `testRunAllFunProofs` (21 groups) / `testRunAllInfProofs` (11 groups) —
  per-proof triage in progress (local corpus run at `4b62b1d6fa`).
  `quicksort` group = §18 (confirmed by local repro); the others
  (newBook, blockContracts, javaCard, observer, SmansEtAl, VACID0, VSTTE10,
  FM2024Tutorial, javadl, simpleTests, redux, the InfFlow examples) pending
  classification against the recorded families.

## 5. jmltk bump 1.1.0 → 1.2.1-SNAPSHOT (user request)

- [x] `gradle/libs.versions.toml` bumped; version exists in Sonatype snapshots (updated 2026-11-07)
- [x] `:key.core:compileJava` green
- [x] `speclang.*` slice: 299 tests / 2 failed (the 2 known JMLParserExceptionTest cases) / 10 skipped — no new failures
- [x] A/B: the 2 known cases fail under 1.1.0- and 1.2.1-SNAPSHOT alike (different failure mode, same 2 cases)
- [x] **1.2.1 parses comment-form merge points into a new `JmlMergePointStmt`**
  (`com.github.javaparser.ast.jml.stmt`, added in 1.2.1) instead of leaving them as
  leftover comments; the converter had no handler → `MergeRuleTests` 9× "Load failed"
  (Unsupported element `SimpleName` from the node's `jmlTags`). A/B-confirmed: 1.1.0
  green, 1.2.1 red, same code otherwise.
- [x] **FIXED**: added `JP2KeYConverter.visit(JmlMergePointStmt)` (temp boolean
  location var, like the fallback form) + `JMLSpecExtractor`/`JMLSpecFactory`
  `createJMLMergeContracts` overload (re-serializes the node's proc/lattice/predicate
  metadata to the textual `merge_point` and re-parses it). `MergeRuleTests` 12/12 +
  `PredicateAbstractionLatticeTests` 3/3 green under 1.2.1.
- [x] Re-run the §1 baseline under 1.2.1-SNAPSHOT + handler (`53dcefd914`):
  **11 failures (was 14), all recorded — 3 resolved** (`LoopScopeInvRuleTests`,
  `arrayMax.key`, `polishFlagSort.key`, all the loop-invariant regression),
  **no new failures**; `KeyJavaPipelineTest` 142/0 (goldens unchanged).
- [x] Commit the bump + handler together (`53dcefd914`)

## Final state at branch tip `53dcefd914`

| Job | Result |
|---|---|
| `keyext.slicing` | **17/17 green** (was 5 red) |
| `keyext.caching` | 1 failure — `TestReferenceSearcher`, the recorded `relax.proof` gap (JMLTK_GAPS §10); `ProofCachingSingleRunTest` green |
| `key.core` | 11 failures, **all recorded** (JMLTK_GAPS §4 store-ref ×4, §5 `\sum` ×2, §10 relax replays ×2, §11 MT ×1, + the 2 known `JMLParserExceptionTest` cases); 3 recorded reds resolved by `6a07c20e63` |
| integration | triaged at `4b62b1d6fa` (CI 2026-11-08): `testRunAllWdProofs` **green** (was red); `testMt2w/4w` = recorded §4/§5 gaps via the curated small-MT collections; `testMtStress` = new pre-existing quicksort load gap (JMLTK_GAPS §18); `testRunAllFunProofs`/`testRunAllInfProofs` per-proof triage in progress |
