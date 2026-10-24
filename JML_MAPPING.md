# JML_MAPPING — TextualJMLConstruct usage in KeY ↔ JMLtk AST equivalents

Branch: `weigl/jmltk-jml`. Status: verified against the published
`jmlparser-core:3.28.2-J8.0-K13.5-SNAPSHOT` (live probes) and the JMLtk grammar
(`javaparser-core/src/main/javacc/java.jj`, origin/main).

This document is the concrete basis for the rewrite in `PLAN.md`: it lists every
place KeY works with `TextualJML*` and which `com.github.javaparser.ast.jml`
(and `ast.key`) class replaces it. "Gap" = construct KeY currently parses that
the published JMLtk grammar does not (verified by probe).

---

## Part A — KeY code working with TextualJML*

### A.1 Producers (construct creation)

| File | What it produces |
|---|---|
| `speclang/njml/PreParser.java` | entry point: JML *text* → `ImmutableList<TextualJMLConstruct>` (parses with KeY's ANTLR grammar, wraps in `TextualJMLConstruct` subclasses) |
| `speclang/njml/TextualTranslator.java` | ANTLR visitor → `TextualJMLSpecCase` (clauses via `TextualJMLSpecCase.Clause/ClauseHd`), `TextualJMLClassInv/ClassAxiom/Initially/Represents/Depends/FieldDecl/MethodDecl/LoopSpec/AssertStatement/SetStatement`, `TextualJMLModifierList`, `Behavior`. Creates `TextualJMLDepends` from `accessible lhs: rhs \measured_by` (class-level "depends" on model fields) |
| `java/transformations/pipeline/JMLTransformer.java` | runs `PreParser` over JML comment text; attaches results to JavaParser `DataKey`s: `KEY_SPEC_CASE` (`List<TextualJMLConstruct>`), `KEY_CLASS_SPEC` (same), `KEY_LOOP_SPEC` (`List<TextualJMLLoopSpec>`); also *executes* model/ghost field declarations and model methods into real (KeY-side synthesized) declarations, builds `JmlAssert`/`set` statement transformations |
| `java/transformations/MarkerStatementHelper.java` | `DataKey<TextualJMLMergePointDecl> KEY_MERGE_POINT`, `DataKey<TextualJMLAssertStatement> KEY_ASSERT` on transformed statement nodes |

### A.2 Carriers between JMLtk AST and KeY AST

| File | Role |
|---|---|
| `java/loader/JP2KeYConverter.java` | moves the `TextualJML*` lists out of JavaParser `DataKey`s into KeY's own AST via `attachedJml` (see A.3); builds KeY `JmlAssert` statements from `KEY_ASSERT`; `KeyMergePointStmt`-relevant code from `KEY_MERGE_POINT`; helpers `getSpec(Node)` / `getLoopSpec(Node)` / `getClassSpec(Node)` |
| `java/ast/ProgramElement.java` (+ `declaration/*`, `statement/*`) | KeY AST nodes carrying `attachedJml : ImmutableList<TextualJMLConstruct>` |

### A.3 KeY AST nodes with `attachedJml`

`ProgramElement` + subclasses: `TypeDeclaration`, `ClassDeclaration`, `InterfaceDeclaration`, `JavaDeclaration`, `MethodDeclaration`, `ConstructorDeclaration`, `StatementBlock`, `LoopStatement` (`While`/`For`/`EnhancedFor`/`Do`), `MergePointStatement`, `JmlAssert`.

### A.4 Consumers

| File | Consumes |
|---|---|
| `speclang/jml/JMLSpecExtractor.java` | the `attachedJml` dispatcher. Class level: `TextualJMLClassInv` → invariant (+free), `TextualJMLInitially`, `TextualJMLRepresents`, `TextualJMLDepends`, `TextualJMLClassAxiom`. Method level: `TextualJMLMethodDecl` → model methods, `TextualJMLSpecCase` → operation contracts. Blocks: trailing `TextualJMLSpecCase` → block contracts; `TextualJMLMergePointDecl` → merge-point contracts. Loops: `TextualJMLLoopSpec` → loop spec, trailing `TextualJMLSpecCase` → loop contracts |
| `speclang/jml/translation/JMLSpecFactory.java` | the semantic core. Translates `TextualJMLSpecCase` (behavior, `Clause/ClauseHd` clause lists holding `LabeledParserRuleContext`s) + `JMLModifier` lists (spec math modes, visibility) into `Contract`/`ClassInvariant`/`ClassAxiom`/`InitiallyClause`/`LoopSpecification`/`Represents`... via `JmlIO`/`Translator`/`JmlTermFactory`. `JmlFacade.parseClause("assignable \\nothing;")` synthesizes defaults |
| `speclang/jml/JMLInfoExtractor.java` | `TextualJMLModifierList`/modifiers on methods/classes/fields → `JMLModifiers` (pure, strictlyPure, helper, specMathMode, nullableByDefault) |
| `java/ast/statement/JmlAssert.java`, `rule/JmlAssertRule.java` | `TextualJMLAssertStatement.Kind` (ASSERT/ASSUME) + `KeyAst.JMLProofScript` (assertion proof) + label → KeY proof rules |
| `speclang/AbstractAuxiliaryContractImpl.java`, `BlockContractImpl.java`, `LoopContractImpl.java` | indirect only (via `JMLSpecFactory`/term translation); no direct `TextualJML*` fields |

### A.5 Tests exercising the IR

`ContractFactoryTest`, `SetStatementTest`, `njml/NJmlTranslatorTests`, `njml/MethodlevelTranslatorTest`, `njml/TextualTranslatorTest`, `jml/TestJMLPreTranslator`, `jml/pretranslation/TextualJMLAssertStatementTest`.

---

## Part B — Construct mapping (verified)

| KeY `TextualJML*` | Replaced by (JMLtk AST) | Notes / verification |
|---|---|---|
| `TextualJMLSpecCase` (+ `Behavior`, `Clause/ClauseHd` clause lists of `LabeledParserRuleContext`) | `clauses.JmlContract` + `clauses.*Clause` nodes, attached via `NodeWithContracts.getContracts()` on `MethodDeclaration` (method), `BlockStmt` (block contract), loop statements (loop contract), `LambdaExpr` | verified: `/*@ normal_behavior requires/ensures/assignable/signals @*/` on a method → `JmlContract` with `JmlSimpleExprClause` ×2, `JmlMultiExprClause`, `JmlSignalsClause`. Contract has `ContractType` (METHOD/LOOP/LOOP_INV/BLOCK/STATEMENT/LAMBDA), `stmt.Behavior` (BEHAVIOR/NORMAL/EXCEPTIONAL/MODEL/BREAK/CONTINUE/RETURN), jmlTags, modifiers, clauses, subContracts |
| `TextualJMLClassInv` (+`free`) | `body.JmlClassExprDeclaration` with kind `JmlBodyClauseKind.INVARIANT` / `INVARIANT_FREE` | plus `INVARIANT_REDUNDANTLY`; grammar also accepts named form `id: expr` |
| `TextualJMLClassAxiom` | `body.JmlClassExprDeclaration` kind `JmlBodyClauseKind.AXIOM` | |
| `TextualJMLInitially` | `body.JmlClassExprDeclaration` kind `JmlBodyClauseKind.INITIALLY` | "initially_is" legacy not needed |
| KeY `history_constraint` (`CONSTRAINT`) | `body.JmlClassExprDeclaration` kind `JmlBodyClauseKind.CONSTRAINT` / `CONSTRAINT_REDUNDANTLY` | grammar present |
| `TextualJMLRepresents` | `body.JmlRepresentsDeclaration` | verified forms `m = e`, `m <- e` (BACKARROW), `\such_that e` |
| `TextualJMLDepends` (class-level "accessible/depends" on model fields) | `body.JmlClassAccessibleDeclaration` | grammar: `accessible [heaps] var : exprs [\measured_by e] ;`. KeY's own parser only knows `accessible` (the `depends` rule is commented out in `JmlParser.g4`), so no keyword mismatch — both use `accessible`. (Probe of `depends …` failed on both parsers, as expected.) |
| Method-contract `accessible lhs: rhs \measured_by …` (the *method* variant, also routed through `TextualJMLDepends` elsewhere) | clause-level `clauses.JmlAccessibleClause` → `JmlMultiExprClause` (heaps, label, `ExpressionList`, `\measured_by`) | |
| `TextualJMLFieldDecl` (model/ghost fields; also local ghost vars) | class level: `body.JmlFieldDeclaration`; statement level: `stmt.JmlGhostStmt` wrapping the declaration | verified both; `JmlGhostStmt`/`JmlFieldDeclaration` exist |
| `TextualJMLMethodDecl` (model methods) | `body.JmlMethodDeclaration` (wraps a `MethodDeclaration` + optional `JmlContract`) | grammar has `JmlMethodDeclaration`, `JmlMethodSignature`, `JmlBodyClauseKind` |
| `TextualJMLModifierList` / `JMLModifier` | plain `Modifier` with `Modifier.DefaultKeyword.JML_*` attached to the node (`jmlModifiers` grammar: PURE, STRICTLY_PURE, MODEL, GHOST, HELPER, NON_NULL, NULLABLE, NULLABLE_BY_DEFAULT, SPEC_*, INSTANCE, NO_STATE, TWO_STATE, NONNULLELEMENTS, math modes, CODE, PEER, REP, READ_ONLY, IMMUTABLE) | `JMLModifier` enum → `DefaultKeyword` mapping already exists in the jar; no carrier class needed |
| `TextualJMLLoopSpec` | `JmlContract` with `ContractType.LOOP_INV` attached to `WhileStmt`/`ForStmt`/`EnhancedForStmt` (loop_invariant(_free) → `JmlSimpleExprClause`, decreases → `JmlSimpleExprClause`, assignable → `JmlMultiExprClause`, loop_determines/loop_separates → info-flow) | verified on `WhileStmt` and `ForStmt` |
| `TextualJMLAssertStatement` (assert/assume + optional label + proof script) | `stmt.JmlExpressionStmt` for `assert`/`assume`/`hence_by`/`assert_redundantly`; standalone label as `stmt.JmlLabelStmt` (JML standard prefix form `/*@ L1: assert e; @*/`) | **Gap**: KeY's inline label `assert LAB: e` and the KeY `BY …` assertion proof (`KeyAst.JMLProofScript`) are not in JMLtk's statement grammar |
| `TextualJMLSetStatement` | `stmt.JmlExpressionStmt` (set → `JmlExpressionStmt` with SET keyword) | verified |
| `TextualJMLMergePointDecl` | `com.github.javaparser.ast.key.KeyMergePointStmt` (`merge_point ( expr ) ;` as a **plain Java statement**, not a JML comment) | **Gap**: KeY writes `//@ merge_point;` / `//@ merge_point (…)` inside JML comments; JMLtk only parses the raw-Java form. Note JMLtk ships a full `ast.key` package (`KeyExecStmt`, `KeyMarkerStatement`, `KeyCcatch*`, `KeyLoopScopeBlockStmt`, `KeyMethodBodyStatement`, `KeyMethodSignature`, `KeyEscapeExpression`, `KeyPassiveExpression`, …) for KeY's DSL statements |
| `LabeledParserRuleContext` (ANTLR ctx + origin term labels) | no JMLtk counterpart needed — replaced by the JML AST node + a thin KeY carrier (node + `OriginTermLabel`/location), or read from `Node.getRange()` | position mapping JMLtk `TokenRange` → KeY `Location` is a Phase-2 task |
| `jml/pretranslation/` package (`Behavior`, `JMLModifier`, all `TextualJML*`) | delete | replaced by `ast.jml` + `ast.key` |

---

## Part C — Clause-level mapping (`TextualJMLSpecCase.Clause/ClauseHd` → JMLtk clause AST)

| KeY clause (Clause/ClauseHd) | JMLtk clause class | kind token |
|---|---|---|
| REQUIRES / REQUIRES_FREE | `clauses.JmlSimpleExprClause` | `JmlClauseKind.REQUIRES`/`REQUIRES_FREE` (+`_REDUNDANTLY`) |
| ENSURES / ENSURES_FREE | `clauses.JmlSimpleExprClause` | `JmlClauseKind.ENSURES`/`ENSURES_FREE` |
| ASSIGNABLE / ASSIGNABLE_FREE | `clauses.JmlMultiExprClause` | `ASSIGNABLE`/`MODIFIABLE`/`MODIFIES` (+`_REDUNDANTLY`); free via keyword |
| ACCESSIBLE | `clauses.JmlMultiExprClause` (via `JmlAccessibleClause`: heaps, `lbl:`, exprs, `\measured_by`) | `ACCESSIBLE` |
| SIGNALS | `clauses.JmlSignalsClause` (exception `Parameter` incl. union types `A|B`, optional var id, optional label) | `SIGNALS` |
| SIGNALS_ONLY | `clauses.JmlSignalsOnlyClause` (type list) | `SIGNALS_ONLY` |
| DIVERGES | `clauses.JmlMultiExprClause` | `DIVERGES` |
| MEASURED_BY | `clauses.JmlMultiExprClause` | `MEASURED_BY` |
| DECREASES | `clauses.JmlSimpleExprClause` | `DECREASES`/`DECREASING` |
| BREAKS / CONTINUES | `clauses.JmlLabeledClause` (label + expr) | `BREAKS`/`CONTINUES` |
| RETURNS | `clauses.JmlSimpleExprClause` | `RETURNS` |
| INFORMATION_FLOW (determines / separates) | `clauses.JmlInfFlowClause` | `DETERMINES`/`SEPARATES`(+`DECLASSIFIES`/`ERASES`/`NEW_OBJECTS`); loop forms `LOOP_DETERMINES`/`LOOP_SEPARATES` |
| CALLABLE (KeY extension, clause-level) | `clauses.JmlCallableClause` | `CALLABLE` |
| KeY `old_clause`/`forall` (clause-local var decls) | `clauses.JmlOldClause` / `clauses.JmlForallClause` | `OLD` / `FORALL` |
| heap prefix `targetHeap` (`\cleanRequired ...`) | `JmlSimpleExprClause`/`JmlMultiExprClause` carry `heaps : NodeList<SimpleName>` (`JmlHeaps`: `<LT> name <GT>`) | — |
| clause name label `lbl: expr` | `JmlClause.getLabel()` (`SimpleName`) on Simple/Multi expr clauses | — |

KeY clause keywords that JMLtk's grammar lacks (**Gap**): `when`, `duration`,
`working_space`, `captures` — note KeY's own `TextualTranslator` already
rejects `duration`/`when` ("not supported by KeY"), so only `working_space`
and `captures` would be real new losses; `spec_name` (`name_clause`) also
absent.

---

## Part D — Verified gap list (published snapshot, live probes)

1. **`merge_point`**: JMLtk parses only the raw-Java `merge_point ( expr ) ;`
   (`ast.key.KeyMergePointStmt`); KeY's `//@ merge_point …` comment form is
   rejected by `JmlProcessor` at method level.
2. **Assert labels**: KeY `//@ assert LAB: e;` (label after `assert`, per
   `JmlParser.g4` `assert_statement`) rejected; JMLtk only supports the JML
   standard prefix-label form `//@ LAB: assert e;` (`JmlLabelStmt` +
   `JmlExpressionStmt`).
3. **Assertion proof scripts**: KeY's `//@ assert e /_proofScript … /` /
   `BY …` (`JmlParser.g4` `assertionProof`, `KeyAst.JMLProofScript`) not in
   JMLtk's `JmlStatement`.
4. **`nowarn` / `debug` pragma-statements** (`JmlParser.g4`): tokens absent.
5. **Datagroup / monitor clauses** (`monitors_for`, `readable_if`,
   `writable_if`, `in_group`, `maps_into`, `datagroup`): tokens absent — worse,
   a probe shows `//@ monitors_for g;` and `//@ readable_if g;` silently
   mis-parse into a spurious `JmlFieldDeclaration`. KeY must reject or
   pre-filter these to avoid corruption.
6. **`\strictly_nothing`** (KeY's `STRICTLY_NOTHING` in assignable): no token;
   JMLtk also parses `\nothing`/`\everything` as plain `NameExpr` (kept as
   expressions — the special meaning must be re-added in KeY's term
   translation).
7. **`captures`, `when`, `duration`, `working_space`, `spec_name`** clauses
   (see Part C).

Non-gaps confirmed empirically: `determines … \by …` at method level, loop
contracts on `while`/`for`, block contracts on `{ … }`, labeled clauses,
`signals_only`, `model`/`ghost` fields, `represents`, `accessible var: …`,
`invariant(_free)`, `initially`, `axiom`, `constraint`, `hence_by`,
`assert_redundantly`, all `Behavior` kinds, JML modifiers incl. math modes.

---

## Part E — Integration notes for the rewrite (Phase 1/2)

- `JavaParserFactory`/`JavaService` must build the parser with
  `new ParserConfiguration().setProcessJml(true)` (and `setJmlKeys` for
  `+KEY`/`-KEY`/`+OPENJML`, `setKeepJmlDocs(true)` while debugging).
- `JmlProcessor` (post-parse visitor) is what rewrites `JmlDoc` into the
  attached JML AST; it runs once per configured key set and warns/removes
  leftover `JmlDoc` when `keepJmlDocs == false`. In an all-fail scenario a
  method-level comment surfaces as `Could not handle the JML comment` problem.
- The method/block/loop contract attachment points to read in
  `JMLSpecExtractor`-equivalents:
  - `MethodDeclaration.getContracts()` / `ConstructorDeclaration.getContracts()`
  - `BlockStmt.getContracts()` (block contracts), loop statements
    (`WhileStmt`/`ForStmt`/`EnhancedForStmt`/`DoStmt`) `.getContracts()`
  - class members (`ClassOrInterfaceDeclaration.getMembers()`) hold the
    `body.Jml*Declaration` nodes
  - statements inside `BlockStmt.getStatements()` hold `JmlExpressionStmt`,
    `JmlGhostStmt`, `JmlLabelStmt` (+ following statement), `JmlUnreachableStmt`
  - KeY DSL statements exist as raw `ast.key` statement nodes
- `JP2KeYConverter`'s `attachedJml` becomes a carrier of `ast.jml`/`ast.key`
  nodes; `JMLSpecFactory` + a new JML-AST→`JTerm` translator replace
  `Translator`/`JmlTermFactory`. Position mapping: JMLtk `TokenRange` →
  KeY `Location` (block-mapping logic reuse).
