# HANDOFF — JMLtk front-end rewrite (PR #3997, branch `weigl/jmltk-jml`)

> Checkpoint taken 2026-10-24 (session end — user went to sleep). This file is
> the durable handoff for the next session. Read `PLAN.md` for the full
> architecture; this file records the *current state* and the open decision.

## 1. Where things stand

- **Branch:** `weigl/jmltk-jml` — **HEAD `74b68f6f82`** ("Phase 1: swap KeY's
  front-end onto the JMLtk AST"), pushed to origin.
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

## 5. OPEN DECISION (user paused; resume here)

User: *"stop for now. I go to sleep. save the plan and the current state, so
you can continue."* → ask on resume which Phase 2 direction to take:

- **Option A — full Phase 2 translator (PLAN.md §196):** new translator walking
  `JmlExpression`/`JmlClause` directly → `JTerm`/`LocationAccess`, porting
  `Translator`/`JmlTermFactory` semantics (operators via
  `OverloadedOperatorHandler`, quantifiers, `\old`, `\result`, `\fresh`,
  seq/map ops, math modes, backtick DL…). Largest path; enables Phase 3 to
  delete `JmlLexer.g4`/`JmlParser.g4` + `speclang/njml` + `pretranslation`.
- **Option B — bridge-is-the-semantics:** the `JmlToTextual` re-parse already
  preserves semantics (same `JmlParser.g4` rules the old `PreParser` used);
  keep the bridge, then delete only provably dead `TextualJML*`/njml code and
  tighten `PLAN.md` accordingly. Smaller, much lower risk.
- **Phase 3** (either way): delete `preparser`/`TextualTranslator`/unused
  `TextualJML*`/grammars; **Phase 4**: delete `SpecificationRepository`
  (specs stay on the AST, rewritten by the pipeline). Testing unlocks at
  Phase 3.

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

1. `git status` clean? (should be — all Phase 1 work committed at `74b68f6f82`).
2. Confirm the Phase 2 fork with the user (§5).
3. Then either start the new translator (Option A, commit a skeleton early) or
   begin Phase-3-safe deletions (Option B: `grep -rn "new TextualJML"` — after
   Phase 1 only `JmlToTextual`/factory should construct them anymore).
4. Keep `:key.core:compileJava` green; commit regularly.
