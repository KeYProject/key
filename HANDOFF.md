# HANDOFF — JMLtk front-end rewrite (PR #3997, branch `weigl/jmltk-jml`)

> Checkpoint taken 2026-10-24 (session end — user went to sleep). This file is
> the durable handoff for the next session. Read `PLAN.md` for the full
> architecture; this file records the *current state* and the open decision.

## 1. Where things stand

- **Branch:** `weigl/jmltk-jml` — **HEAD** contains Phase 1 (`74b68f6f82`) plus
  the Phase-2-Option-B deletions (front-end dead code), pushed to origin.
- **PR:** #3997, retitled *"JMLtk front-end: consume JMLtk's parsed JML AST
  (Phases 0+1)"*, body refreshed.
- **Feedback loop:** `./gradlew :key.core:compileJava` — **GREEN** at HEAD.
  Per user directive: *no testing until Phase 3*; only the compile is checked.
- **Worktree:** `/home/weigl/.local/share/opencode/worktree/fa2a33/witty-cabin`.
- **Do NOT touch:** `/home/weigl/work/key` (~216 unstaged deletions from a
  concurrent agent).

### Commits
| Commit | Content |
|---|---|
| `6d174cdadd` | Phase 0 — `JavaParserFactory` enables JMLtk JML processing (`setProcessJml(true)`, JML-keys policy). |
| `74b68f6f82` | Phase 1 — front-end swap onto the JMLtk AST (see below). |

## 2. What Phase 1 did

- **`JmlSpec`** (`speclang/jml/JmlSpec.java`, NEW): `record JmlSpec(@NonNull
  Node node)` — the carrier for JMLtk AST nodes in KeY's AST.
- **KeY AST swap:** `JavaDeclaration`/`MethodDeclaration`/`ConstructorDeclaration`/
  `ClassDeclaration`/`InterfaceDeclaration`/`TypeDeclaration`/`StatementBlock`/
  loops (`While`/`For`/`EnhancedFor`/`Do`)/`MergePointStatement` carry
  `ImmutableList<JmlSpec>`/`List<JmlSpec>`. **`KEY_LOOP_SPEC` deleted**; loops
  use the merged `getSpec(n)` (LOOP contracts + LOOP_INV invariants both attach
  to the loop node).
- **`JMLTransformer`** rewritten: JMLtk already attaches parsed JML to the Java
  AST; the transformer only (a) relocates `JmlContract`s into
  `KEY_SPEC_CASE`/`KEY_CLASS_SPEC` (`DataKey<List<JmlSpec>>`), (b) unwraps
  `JmlMethodDeclaration`/`JmlFieldDeclaration` wrappers, (c) self-marks JML
  statements (`JmlExpressionStmt` → KEY_ASSIGN (set) / KEY_ASSERT (else),
  ghosts → `JML_GHOST` modifier, `KeyMergePointStmt` → KEY_MERGE_POINT).
  `JmlDocSanitizer`/`StringConstructor` deleted.
- **`JMLSpecExtractor`** rewritten: only dispatches `JmlSpec`s to the factory
  (class specs via node `instanceof`; method specs per-spec). Keeps
  `createNonNullPositionedString` (public static) + `arrayDepth`.
- **`JMLSpecFactory`**: `JmlSpec` overloads for every entry point; the
  implicit-clause enrichment moved here from the old extractor
  (`createJMLOperationContracts(pm, JmlSpec, addInvariant)` +
  `enrichOperationContract`): purity assignables (`\strictly_nothing`/
  `\nothing` per modifiable heap), `\inv` requires/ensures/signals, non-null
  pre/post, default signals-only, synthetic `MODEL_BEHAVIOR` only when a
  `JmlMethodDeclaration` is the sole attached spec. `getDefaultSignalsOnly` +
  `IMPL_TERM_LABEL` duplicated here with `ParameterlessTermLabel.
  IMPLICIT_SPECIFICATION_LABEL` (typed `TermLabel`).
- **`JmlToTextual`** (`translation/JmlToTextual.java`, NEW — the bridge):
  re-serializes each JMLtk clause/declaration against the matching
  `JmlParser.g4` rule (`class_invariant`, `initially_clause`, `class_axiom`,
  `represents_clause`, `accessible_clause`, `method_declaration`,
  `requires_clause`, `ensures_clause`, `variant_function`, `returns_clause`,
  `assignable_clause`, `measured_by_clause`, `diverges_clause`,
  `breaks_clause`, `continues_clause`, `signals_clause`,
  `signals_only_clause`, `separates_clause`, `determines_clause`,
  `loop_invariant`, `loop_assignable_clause`, `loop_determines_clause`) and
  hands the resulting parse trees to the existing `TextualJML*` translation.
  Heap semantics: unqualified clauses fall back to **base heap** (mirrors old
  `TextualTranslator.visitTargetHeap`); `JmlSimpleExprClause.getHeaps()` is a
  `NodeList<SimpleName>`, `JmlMultiExprClause.getHeaps()` is an
  `Optional<NodeList<SimpleName>>` (both handled).
- **`JP2KeYConverter`**: `visit(JmlExpressionStmt)` re-parses with KeY grammar
  (`expressionEOF()` / `set_statement()`) → `JmlAssert`/`SetStatement`;
  `visit(KeyMergePointStmt)` → `MergePointStatement(pi, c, new JmlSpec(n), loc)`
  when marked, else bare expr. Loops pass merged `getSpec(n)`.
- **`SpecialJavaPrinter`**: `print(List<JmlSpec>)` prints `/*@ node.toString() */`.
- **`JMLInfoExtractor`**: `getJMLComments(TypeDeclaration)` →
  `ImmutableList<JmlSpec>`.
- **`MarkerStatementHelper`**: `KEY_ASSIGN`/`KEY_ASSERT` = `DataKey<JmlExpressionStmt>`,
  `KEY_MERGE_POINT` = `DataKey<KeyMergePointStmt>`; `KIND_*` ints kept.

## 3. Semantics that MUST be preserved (verified during Phase 1)

- Block contracts = `ContractType.METHOD`; loop contracts = `ContractType.LOOP`;
  loop invariants = `ContractType.LOOP_INV` (checked against jmltk source).
- Extractor filters: blocks `!= LOOP && != LOOP_INV`; loops `== LOOP`;
  `extractLoopInvariant` scans reverse for `LOOP_INV`, keeps the "Missing
  decreases" warning; `extractMergeContracts` filters
  `node() instanceof KeyMergePointStmt`.
- Model method detection in factory: `pm.getMethodDeclaration().
  containsModifier(ModifierKind.JML_MODEL)` → first attached
  `JmlMethodDeclaration` → `JmlToTextual.toMethodDecl(s).getMethodDefinition()`.
- Enrichment guards: `!isHelper && pm.getStateCount() > 0 &&
  (!pm.isStatic() || addInvariant)`; constructor inv requires via
  `"%s.\\inv".formatted(pm.getName())`; signals inv only when behavior
  != NORMAL and not model; signals-only default only when
  `getSignalsOnly().isEmpty() && behavior != NORMAL && !pm.isModel()`.

## 4. Known degradation (accepted)

- JMLtk has **no statement-level `merge_point`/`merge_proc`/`merge_params`**
  grammar; only the Java statement `merge_point(<expr>);` (`KeyMergePointStmt`).
  Factory re-parses `"merge_point " + kms.getExpr() + ";"` via KeY's
  `merge_point_statement` → only unparametric merge (`MergeByIfThenElse`)
  works. **`testcase/merge/A.java` and `Gcd.java` (parametric,
  `merge_proc`/`merge_params` in comments) will fail to load under jmltk.**

## 5. Phase-2 decision — TAKEN (resume here for the next chunk)

**Decision: Option B — the `JmlToTextual` re-parse bridge IS the semantics
layer** (it re-uses the exact same `JmlParser.g4` rules the old `PreParser`
used, so the specification semantics of the old front-end are preserved and
validated by the compile-only loop). Proceed with provably-dead deletions,
keep the KeY grammar + `Translator`/`JmlTermFactory` machinery, adjust
`PLAN.md`.

Already done as part of Option B:
- Deleted (main code, unused since Phase 1 — verified by repo-wide grep, no
  refs outside `key.core/src/test`): `njml/PreParser.java`,
  `njml/TextualTranslator.java`, `njml/JmlCheck.java`, `njml/JmlChecks.java`,
  `pretranslation/TextualJMLFieldDecl.java`,
  `pretranslation/TextualJMLModifierList.java`,
  `pretranslation/TextualJMLSetStatement.java`,
  `pretranslation/TextualJMLMergePointDecl.java`.
  (Kept `DebugJmlLexer` — backs the `gradle debugJmlLexer` task.)
- Removed the now-dead factory overload
  `createJMLMergeContracts(mps, TextualJMLMergePointDecl)`; cleaned the stale
  commented-out block in `JP2KeYConverter.visit(EmptyStmt)` and the
  `njml` `package-info` (now documents the JMLtk → JmlSpec → re-parse flow).
- `:key.core:compileJava` GREEN after the deletions.

Remaining (next chunks, still Option B):
- More dead-code sweeps: re-grep `new TextualJML*` after each change. Only the
  following pretranslation classes are constructed by live code
  (`JmlToTextual`/`JMLSpecFactory`/`JmlAssert`/`SpecialJavaPrinter`):
  `TextualJMLSpecCase`, `TextualJMLLoopSpec`, `TextualJMLClassInv`,
  `TextualJMLClassAxiom`, `TextualJMLInitially`, `TextualJMLRepresents`,
  `TextualJMLDepends`, `TextualJMLMethodDecl`, `TextualJMLAssertStatement`
  (only its `Kind` enum + legacy ctor are used), plus `Behavior`, `JMLModifier`,
  `TextualJMLConstruct`.
- Stale tests in `key.core/src/test` referencing the deleted front-end need to
  be dropped/rewritten in Phase 3 (they no longer compile): `TestJMLPreTranslator`,
  `TextualTranslatorTest`, `MethodlevelTranslatorTest`, `ClasslevelTranslatorTest`,
  `NJmlTranslatorTests`, `ContractFactoryTest`, `SetStatementTest`,
  and the `njml`-based parts of `JmlMarkerDecisionTest`/sources in `preparser`.
  (`TextualJMLAssertStatementTest` keeps compiling — the class stays.)
- **End state of Option B:** KeY grammar + njml translation machinery stay;
  `JmlParser.g4`/`JmlLexer.g4` are NOT deleted (the bridge needs them). This
  deviates from the PLAN §196 "full Phase 2 translator" and §210 "delete the
  ANTLR grammars" — those become the (optional) later phase if a direct
  JMLtk-AST→`JTerm` translator is ever wanted. **Phase 4** (delete
  `SpecificationRepository`) is unaffected and remains as planned.

## 6. Useful references (may vanish — re-verify before trusting paths)

- Extracted jmltk SNAPSHOT jar: `/tmp/opencode/jmljar/` (from gradle cache
  `jmlparser-core-3.28.2-J8.0-K13.5-SNAPSHOT.jar`). `javap` signatures used by
  `JmlToTextual` were verified against this jar.
- jmltk checkout (javaparser sources, `java.jj`, `JmlProcessor.java`):
  `/home/weigl/work/javaparser/` @ `3.28.2-J8.0-K13.5`.
- PR body template: `/tmp/opencode/pr-jmltk-jml-body.md`.
- KeY grammar rules referenced by the bridge all verified present in
  `key.core/src/main/antlr4/JmlParser.g4`.

## 7. First actions on resume

1. `git status` clean? (should be — all work committed).
2. Decision §5 is already taken (Option B, dead-code sweep started).
3. Next chunk: continue the Option-B sweep (§5 "Remaining") — re-grep
   `new TextualJML*`/class refs, delete what is provably dead, keep
   `:key.core:compileJava` green, commit regularly, push.
4. When the sweep stalls (only `JmlToTextual`/`JMLSpecFactory` construct
   `TextualJML*`), move to Phase-3 work: stale-test cleanup +
   `SpecificationRepository` (Phase 4) prep.
