# PLAN — Rewrite JML specification handling in KeY

Branch: `weigl/jmltk-jml` (created from `weigl/jmltk` @ `c91b316363`)
Status: **draft — agreed to write the design first before coding**

## 1. Goal

Completely rewrite how KeY parses and translates JML specifications, moving from
KeY's own hand-written ANTLR JML parser to JMLtk's JML AST as the front end, and
translating directly from the JML AST to KeY's internal specification language
(`speclang`) objects and dynamic-logic (`JTerm`) terms.

The PR migration rationale ("do not use JMLtk to parse JML yet") is hereby
superseded: `weigl/jmltk-jml` is the branch on which we finally exchange the JML
parsing, as contemplated in the PR #3966 plan ("How to proceed further with
exchanging JML parsing").

## 2. Current state (as of this branch)

### 2.1 JML parsing today — KeY's own ANTLR parser

JML **syntax** is NOT parsed by JMLtk. JMLtk is used only as the Java parser
(fork of JavaParser), and its `ast.jml` surface is used only to (a) capture raw
JML comment text (`JmlDoc*`) and (b) represent in-code JML statements
(`assert`/`assume`/`set` via `JmlExpressionStmt`, `JmlGhostStmt`, ...).

The JML spec language is parsed by KeY's ANTLR grammar:

```
key.core/src/main/antlr4/JmlLexer.g4      (JML tokens, comment modes, +KEY/+OPENJML/-KEY marker decision)
key.core/src/main/antlr4/JmlParser.g4     (spec_case, clause, expr, storeref, quantifiers, \by, \dl, assertionProof)
```
generated into `de.uka.ilkd.key.speclang.njml`.

### 2.2 Pipeline (data flow)

```
.java/.key source
  └─ JavaParserFactory / JavaService (JMLtk)   ─ Java AST, JML captured as JmlDoc
      └─ KeYJavaPipeline (transformations)
          └─ JMLTransformer   ─ sanitizes JmlDoc text, calls PreParser,
                                stores TextualJMLConstructs in JavaParser DataKeys
                                (KEY_SPEC_CASE, KEY_CLASS_SPEC, KEY_LOOP_SPEC)
          └─ JmlDocRemoval    ─ strips JmlDoc nodes afterwards
      └─ JP2KeYConverter     ─ moves TextualJMLConstruct *into KeY AST* via
                               attachedJml fields (declarations, classes, loops,
                               blocks, MergePointStatement); JmlExpressionStmt → JmlAssert/SetStatement
  └─ SLEnvInput.read() → JMLSpecExtractor (SpecExtractor)
      └─ JMLSpecFactory     ─ builds Contract/ClassInvariant/ClassAxiom/InitiallyClause/
                               LoopSpec/BlockContract/MergeContract/DependencyContract
          └─ JmlIO → Translator → JmlTermFactory   ─ JML parse trees → KeY terms (SLExpression/JTerm)
      └─ SpecificationRepository
```

Dotted boxes = the parts this rewrite replaces.

### 2.3 Key classes to be retired / replaced

| Class | Role | Fate |
|---|---|---|
| `speclang/njml/JmlLexer.g4`, `JmlParser.g4` | ANTLR JML grammar | delete when no longer referenced |
| `njml/JmlFacade` | thin ANTLR facade (parseExpr/parseClause) | replaced by JMLtk-driven parts of `JmlIO` |
| `njml/PreParser` | text comment → TextualJMLConstruct | replaced by JMLtk JML parsing |
| `njml/TextualTranslator` | ANTLR visitor → TextualJML* | superseded by JML AST |
| `njml/Translator` | ANTLR visitor → JTerm | rewritten as JML-AST → JTerm translator |
| `njml/JmlTermFactory` | JML ops → DL terms | ported into new translator |
| `njml/LabeledParserRuleContext` | parse tree + TermLabel carrier | replaced by JML-AST + label |
| `speclang/jml/pretranslation/TextualJML*` (13+ classes) | intermediate "textual" constructs | removed or reduced to a thin bridge |
| `njml/JmlMarkerDecision` | +KEY/+OPENJML marker policy | kept (applied on JMLtk text/AST) |
| `njml/JmlChecks`, `JmlCheck` | post-parse warnings | ported to JML-AST checks |
| `njml/SpecMathMode`, `OverloadedOperatorHandler`, `LDT/Integer/Float/DoubleHandler` | semantics helpers | reused by the new translator |

### 2.4 Classes kept as integration seams

`JMLSpecExtractor`, `SpecExtractor`, `SLEnvInput`, `SpecificationRepository`,
`JP2KeYConverter` (attachedJml transfer), `JMLInfoExtractor`, `JMLResolverManager`,
`JMLBuiltInPropertyResolver`, `Context`, `ProgramVariableCollection` — plus the
`speclang` root (`Contract`, `ClassInvariant`, `ClassAxiom`, `InitiallyClause`,
`LoopSpecification`, impls) and `speclang/dl/DLSpecFactory` (`.key` DL specs).

## 3. JMLtk readiness (verified facts)

- JMLtk (jmltoolkit/jmltk) `javaparser-core/src/main/javacc/java.jj` **contains**
  full JML grammar productions since 2021: `JmlContracts`, `JmlContractM`,
  `JmlContractClause`, `JmlLoopContract`, `JmlInvContract`, `JmlRefiningContract`,
  `JmlModelProgram`, contract clauses (requires/ensures/assignable/accessible/
  determined/measured_by/callable/signals/signals_only), etc.
- The **published jar** KeY consumes
  `io.github.jmltoolkit:jmlparser-core:3.28.2-J8.0-K13.5-SNAPSHOT`
  (mavenCentral + sonatype snapshots) does **NOT** contain the contract
  productions: bytecode inspection of `GeneratedJavaParser` finds 0 hits for
  `JmlContractM/JmlContractsM/JmlContractClause/...`; a live parse of a JML
  contract yields only `JmlDoc/JmlDocDeclaration` (opaque), no `JmlContract`.
- The jar ships the complete JML AST (`ast.jml.body/clauses/expr/stmt/doc`, 67
  classes: `JmlContract`, `JmlClause`, `JmlExpression`, `JmlGhostStmt`, ...) and
  `com.github.javaparser.jml.JmlDocSanitizer`.
- In-code JML statements are already parsed (`JmlExpressionStmt`, `JmlGhostStmt`,
  `JmlLabelStmt`, `JmlUnreachableStmt`, `JmlRefiningStmt`).

**Conclusion:** the JML grammar largely exists upstream but is (a) not in the
published artifact and (b) of 2021 vintage, so it must be validated/extended
against the JML KeY actually supports today.

## 4. Target architecture

```
.java (JML in comments)
  └─ JMLtk                       ─ Java AST *with* JML AST (JmlContract/JmlClause/JmlExpression)
      └─ JMLTransformer (adapted)
          └─ JP2KeYConverter     ─ JML AST chunks attached to KeY AST (attachedJml)
  └─ SLEnvInput.read() → JMLSpecExtractor
      └─ JMLSpecFactory (rewritten to consume JmlContract/JmlClause)
          └─ JML-AST Translator (new; replaces Translator+JmlTermFactory) → JTerm
      └─ SpecificationRepository
```

Design principles:

1. **JMLtk owns JML syntax.** KeY stops grammatically parsing JML. JMLtk produces
   `JmlContract` (method/loop/invariant), `JmlClause`, and `JmlExpression` nodes,
   attached to the declarations/statements they specify. JML comments are still
   recoverable for error messages via `JmlDoc`/JMLtk's `JmlDocSanitizer`.
2. **Semantics stay in KeY.** KeY's `JMLSpecFactory` and a new JML-AST→JTerm
   translator implement KeY's interpretation of JML (spec math modes, LDT
   wiring, KeY extensions `\by`, backtick DL terms, `\dl_...`), mirrored from
   the current `Translator`/`JmlTermFactory`/`JMLSpecFactory`.
3. **One bridge type.** Replace the ANTLR-context carrier `LabeledParserRuleContext`
   with a JML-AST carrier that pairs a JML node with origin labels/positions, so
   `attachedJml` and clause-level plumbing change once.
4. **Tests are the contract.** The JML test suite below specifies "JML KeY
   supports". Parity = those tests pass against JML-AST-driven code. Where the
   AST makes semantics cleaner, tests may be adjusted only with recorded reason.

## 5. Phases

### Phase 0 — JMLtk grammar: validate, extend, publish
Goal: `jmlparser-core:...SNAPSHOT` that parses the JML KeY needs.
- Build `jmlparser-core` from jmltoolkit/jmltk `main`; write a probe that parses
  a corpus of JML (contracts, invariants, represents, model/ghost fields, loop
  specs, old/quantified ops, signaals/signals_only, info-flow, specs on
  statements) and reports which constructs yield a clean `Jml*` AST.
- Gap-fill the grammar (likely additions): KeY markers `+KEY`/`-KEY`/`+OPENJML`
  handling, `\by separates/determined` info-flow syntax, backtick `KEY_TERM`
  escapes (or keep them opaque), spec math mode keywords, KeY built-ins
  (`\dl_*`, `\inv`, `\nonnullelements`, ...), `//@` and nested `@`-line JML
  across multiple comment runs.
- Decide marker policy: prefer JMLtk-side lexer support; fall back to KeY-side
  filtering of `JmlDoc` text before AST construction.
- Coordinate with jmltoolkit: open upstream issues/PR; publish a new snapshot
  version (bump suffix, e.g. `-K13.6-SNAPSHOT` or Zeit-or-new-snapshot) to
  Sonatype snapshots; update `gradle/libs.versions.toml` in KeY.
- Deliverable: KeY `./gradlew :key.core:test --tests "*.njml.*"`-style probe on a
  spike that demonstrates `JmlContract` on `MethodDeclaration` for the corpus.

### Phase 1 — Front-end swap on KeY side
- Adapt `JMLTransformer` (and friends: `JmlDocRemoval`, `RecordClassBuilder`,
  `ConstantStringExpressionEvaluator`) to consume JMLtk JML AST instead of raw
  `JmlDoc` + `PreParser`. Reuse JMLtk's `JmlDocSanitizer` if it covers KeY needs.
- Replace `LabeledParserRuleContext`/`TextualJML*` with JML-AST-based carriers
  through `JP2KeYConverter`'s `attachedJml`.
- `JMLSpecExtractor` unchanged in shape (reads attached JML); `JMLSpecFactory`
  input type swaps from `TextualJML*` to JML AST.

### Phase 2 — Semantic translation rewrite
- New `JMLSpecFactory` paths: `JmlContract` → `FunctionalOperationContract`,
  `BlockContract`, `LoopContract`, `MergeContract`, `DependencyContract`;
  `JmlInvContract`/represents/initially/model fields → `ClassInvariant`,
  `ClassAxiom`/`Represents`, `InitiallyClause`, model/ghost field materialization.
- New translator walking `JmlExpression`/`JmlClause`/store-refs → `JTerm`/
  `LocationAccess`-sets, porting semantics from `Translator`/`JmlTermFactory`
  (operators via `OverloadedOperatorHandler`, quantifiers, `\old/_PRE`, `\result`,
  `\fresh`, `\typeof`, seq/map ops, `\seq_def`, math modes, JML built-ins,
  `\by`, backtick DL).
- Error reporting: keep message/position quality; map positions from JMLtk
  ranges back into the `.key`/`.java` file (reuse existing block-mapping logic).

### Phase 3 — Deletion & parity
- Remove ANTLR grammars `JmlLexer.g4/JmlParser.g4` and now-unused njml classes
  (`PreParser`, `TextualTranslator`, old `Translator`, `JmlTermFactory` legacy
  paths, `TextualJML*` if fully superseded).
- Update tests in §6 to the new pipeline; fix behaviors that legitimately
  change; keep the full `key.core`/`key.ui` test run green on CI.
- Remove `.jml`-file special-casing only if JMLtk-based loading covers it;
  otherwise document the remaining gap.

## 6. Regression net (tests defining KeY-supported JML)

`key.core/src/test/java/de/uka/ilkd/key/speclang/`:
- `njml/NJmlTranslatorTests`, `njml/ClasslevelTranslatorTest`,
  `njml/MethodlevelTranslatorTest`, `njml/TextualTranslatorTest`,
  `njml/ExpressionTranslatorTest`, `njml/ModifiersTest`,
  `njml/ContractLoadingTests`, `njml/JMLParserExceptionTest`
- `jml/TestJMLPreTranslator`, `jml/TestJMLTranslator`, `jml/JmlMarkerDecisionTest`,
  `jml/pretranslation/TextualJMLAssertStatementTest`
- `SetStatementTest`, `ContractFactoryTest`, `ContentOrderNumberingTest`
- related: `key.core/src/test/java/TranslationTest.java`,
  `KeyJavaPipelineTest.java`, `ReduxTest.java`,
  `key.core/src/test/java/de/uka/ilkd/key/parser/TestJMLParserAssociativity.java`

Fixtures: `key.core/src/test/resources/de/uka/ilkd/key/speclang/` (incl.
`njml/exceptional/`).

## 7. Open questions

1. Marker policy (`+KEY`/`-KEY`/`+OPENJML`): JMLtk lexer vs KeY-side text filter.
2. Do we keep `TextualJML*` as a thin serialization/AST bridge, or cut them
   entirely? (They currently couple KeY AST → speclang translation.)
3. `\by separates/determined` (KeY-specific): grammar extension in JMLtk vs
   tolerated-opaque-JML handling in KeY.
4. Separate `.jml`/`.spec` files: parse via JMLtk with which enclosing context?
5. Versioning/publishing of the new JML-enabled snapshot (owner: jmltoolkit).
6. License header policy for new files on this branch (repo convention
   GPL-2.0-or-later vs current -only drift).
7. Performance: JMLtk parse time with full JML grammar on large files.

## 8. Immediate next step (after this doc)

Phase 0 spike: build `jmlparser-core` from jmltoolkit/jmltk `main`
(`~/.gradle`-independent, into a local dir or a jmltk worktree), run the JML
corpus probe, and report which constructs parse into `Jml*` AST vs are missing.
Then decide gap-fill list and coordinate publishing.
