# JML_MAPPING — JML constructs: KeY front-end ↔ JMLtk AST equivalents

Branch: `weigl/jmltk-jml`. Status: **updated for the shipped architecture**
(HEAD `d7fdfe737c`): JML is parsed by JMLtk and consumed from its typed AST
directly; there is no `TextualJML*` production from comments and no
`attachedJml`/`JmlSpec` carrier (see PLAN.md §2.2/§4). Doing so was verified
against the published `jmlparser-core:3.28.2-J8.0-K13.5-SNAPSHOT` (live
probes) and the JMLtk grammar (`javaparser-core/src/main/javacc/java.jj`,
origin/main).

This document is the concrete basis for the rewrite in `PLAN.md`: it maps
every JML construct KeY supports to its `com.github.javaparser.ast.jml`
(and `ast.key`) class. Parts B–D (construct mapping, clause mapping, gap
list) are the reference. Part A is HISTORICAL for the deleted producers but
its consumer entries were rewritten to the shipped design. "Gap" = construct
KeY currently parses that the published JMLtk grammar does not (verified by
probe).

---

## Part A — KeY code working with JML (shipped design)

### A.1 Producers (JML parsing)

| File | What it produces |
|---|---|
| JMLtk `JmlProcessor` (via `JavaParserFactory`, `setProcessJml(true)`) | the **single** JML parser: attaches `JmlContract` (via `NodeWithContracts`), `JmlClassLevelDeclaration` members, `JmlMethodDeclaration`/`JmlFieldDeclaration` wrappers, and `JmlExpressionStmt`/`JmlGhostStmt`/`KeyMergePointStmt` statements directly to the Java AST |
| `java/transformations/pipeline/JMLTransformer.java` | re-processes method bodies: unwraps `JmlMethodDeclaration`/`JmlFieldDeclaration` into their contained declarations (remembered via the `KEY_JML_WRAPPER` data key), self-marks JML statements (`KEY_ASSERT`/`KEY_ASSIGN`/`KEY_MERGE_POINT`) |
| `speclang/jml/translation/JmlToTextual.java` | produces the `TextualJML*` **semantics** layer: re-serializes each JMLtk clause/declaration and re-parses it with KeY's `JmlParser.g4` rules for `Translator`/`JmlTermFactory` |

### A.2 Carriers between JMLtk AST and KeY AST

| File | Role |
|---|---|
| `java/KeYJPMapping.java` (`registerReverse`, `nodeFromKeY`) | the **only** bridge: `JP2KeYConverter` registers KeY `TypeDeclaration` → JMLtk `JmlTypeDeclaration` and KeY method/ctor → contract carrier; the extractor resolves the JMLtk nodes back from the KeY AST. No `attachedJml`, no `JmlSpec` |
| `java/loader/JP2KeYConverter.java` | converts the Java declarations (skipping pure class-level JML spec members); `JmlExpressionStmt` → `JmlAssert`/`SetStatement` and `KeyMergePointStmt` → `MergePointStatement` via KeY-grammar re-parse; keeps model/ghost wrappers reachable as the contract carrier |

### A.3 KeY AST nodes with JML

None carry JML: the KeY AST has no `attachedJml`. JML lives on the JMLtk AST
and is reached via the reverse mapping / the nodes' own position in it.

### A.4 Consumers

| File | Consumes |
|---|---|
| `speclang/jml/JMLSpecExtractor.java` | resolves the JMLtk type/method via `KeYJPMapping.nodeFromKeY` and reads the specs off it: class level (`JmlClassExprDeclaration` → invariant/axiom/initially, `JmlRepresentsDeclaration`, `JmlClassAccessibleDeclaration`), method level (contract carrier; model methods via `JmlToTextual.toMethodDecl(wrapper).getMethodDefinition()`), blocks/loops (attached `JmlContract`, `extractLoopInvariant` scans for `LOOP_INV`), merge points (carrier is `KeyMergePointStmt`) |
| `speclang/jml/translation/JMLSpecFactory.java` | the semantic core. Direct-class overloads (`createJMLOperationContracts(pm, JmlContract, ParserRuleContext modelMethodDefinition, boolean addInvariant)`, `createJMLModelMethodContracts(pm, ParserRuleContext modelMethodDefinition, boolean addInvariant)`, …) build `Contract`/`ClassInvariant`/`ClassAxiom`/`InitiallyClause`/`LoopSpecification`/`Represents`… via `JmlToTextual` → `JmlIO`/`Translator`/`JmlTermFactory`. `JmlFacade.parseClause("assignable \\nothing;")` synthesizes defaults |
| `speclang/jml/JMLInfoExtractor.java` | reads `JMLModifiers`-relevant modifiers off the JMLtk nodes (pure, model, helper, specMathMode, nullableByDefault) |
| `java/ast/statement/JmlAssert.java`, `rule/JmlAssertRule.java` | `JmlAssert` (built by the converter from `JmlExpressionStmt`) + `KeyAst.JMLProofScript` + label → KeY proof rules |
| `speclang/AbstractAuxiliaryContractImpl.java`, `BlockContractImpl.java`, `LoopContractImpl.java` | indirect only (via `JMLSpecFactory`/term translation); no direct JML fields |

### A.5 Tests exercising the front-end

`njml/ClasslevelTranslatorTest`, `njml/ExpressionTranslatorTest`,
`njml/ModifiersTest`, `njml/ContractLoadingTests`, `njml/JMLParserExceptionTest`,
`jml/TestJMLTranslator`, `jml/JmlMarkerDecisionTest`, `SetStatementTest`,
`ContractFactoryTest`, `ContentOrderNumberingTest`.

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
| `TextualJMLAssertStatement` (assert/assume + optional label + proof script) | `stmt.JmlExpressionStmt` for `assert`/`assume`/`hence_by`/`assert_redundantly`; standalone label as `stmt.JmlLabelStmt` (JML standard prefix form `/*@ L1: assert e; @*/`) | **Gap** (deferred): KeY's inline label `assert LAB: e` and the KeY `BY …` assertion proof (`KeyAst.JMLProofScript`) are not in JMLtk's statement grammar; upstream support planned (see Part D.3) |
| `TextualJMLSetStatement` | `stmt.JmlExpressionStmt` (set → `JmlExpressionStmt` with SET keyword) | verified |
| `TextualJMLMergePointDecl` | `com.github.javaparser.ast.key.KeyMergePointStmt` (`merge_point ( expr ) ;` as a **plain Java statement**, not a JML comment) | JMLtk parses the raw-Java form; `JP2KeYConverter` translates it back into KeY's `//@ merge_point …` statement (KeY-authored files keep the comment form). JMLtk ships a full `ast.key` package (`KeyExecStmt`, `KeyMarkerStatement`, `KeyCcatch*`, `KeyLoopScopeBlockStmt`, `KeyMethodBodyStatement`, `KeyMethodSignature`, `KeyEscapeExpression`, `KeyPassiveExpression`, …) for KeY's DSL statements |
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

1. **`merge_point`**: JMLtk parses it only as the raw-Java statement
   `merge_point ( expr ) ;` (`ast.key.KeyMergePointStmt`), not from inside a
   JML comment. **Resolution:** in the new pipeline, `KeyMergePointStmt` is
   translated in `JP2KeYConverter` back into KeY's merge-point statement,
   i.e. the `//@ merge_point …` form KeY files are authored in
   (`MergePointStatement` + its JML marker text). So the comment-form
   incompatibility is neutralized on the KeY side — KeY files keep
   `//@ merge_point`, JMLtk just delivers it as the raw statement node.
2. **Assert labels**: KeY `//@ assert LAB: e;` (label after `assert`, per
   `JmlParser.g4` `assert_statement`) rejected; JMLtk only supports the JML
   standard prefix-label form `//@ LAB: assert e;` (`JmlLabelStmt` +
   `JmlExpressionStmt`).
3. **Assertion proof scripts**: KeY's `//@ assert e /_proofScript … /` /
   `BY …` (`JmlParser.g4` `assertionProof`, `KeyAst.JMLProofScript`) not in
   JMLtk's `JmlStatement`. **Status: intentionally out of scope for KeY-side
   work — JMLtk grammar support is planned upstream (near future).** KeY
   should keep surfacing the raw `JmlDoc` text for these until the upstream
   grammar lands.
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

## Part E — Integration notes (as shipped)

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
- There is no carrier between the ASTs. (HISTORICAL plan text: "`JP2KeYConverter`'s
  `attachedJml` becomes a carrier of `ast.jml`/`ast.key` nodes; `JMLSpecFactory`
  + a new JML-AST→`JTerm` translator replace `Translator`/`JmlTermFactory`.")
  What shipped: the KeY↔JMLtk reverse mapping (`KeYJPMapping.registerReverse` /
  `nodeFromKeY`) is the only bridge; `JMLSpecFactory` consumes the typed classes
  directly and the `JmlToTextual` → `JmlParser.g4` →
  `Translator`/`JmlTermFactory` chain provides the semantics ("Option B" —
  the originally planned direct JML-AST→`JTerm` translator was not built).
  Position mapping: JMLtk `TokenRange` → KeY `Location` (block-mapping logic
  reuse); note that re-parse/building errors currently report
  `<unknown>:1:…`-style positions instead (recorded parity gap, HANDOFF §5.1).
