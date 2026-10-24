# PLAN — Rewrite JML specification handling in KeY

Branch: `weigl/jmltk-jml` (created from `weigl/jmltk` @ `c91b316363`)
Status: **design doc** — approved direction: remove KeY's own JML front-end and
the `TextualJMLConstruct` intermediate representation; use JMLtk's JML AST
(`ast.jml`) directly.

## 1. Goal

Completely rewrite how KeY parses and translates JML specifications:

- **Remove** KeY's hand-written ANTLR JML parser (`JmlLexer.g4`/`JmlParser.g4`)
  and **all** `TextualJMLConstruct`-based intermediate classes
  (`speclang/jml/pretranslation/*`).
- **Use JMLtk's JML AST** (`JmlContract`, `JmlClause`, `JmlExpression`,
  `JmlClassLevelDeclaration`, …) as the single front-end representation.
- **Keep semantics in KeY**: translate from the JML AST to KeY's `speclang`
  objects and dynamic-logic (`JTerm`) terms (`JMLSpecFactory` + a new
  JML-AST→`JTerm` translator).

The PR #3966 migration rationale ("do not use JMLtk to parse JML yet") is
hereby superseded: `weigl/jmltk-jml` is the branch where we finally exchange
the JML parsing, as contemplated in the PR #3966 plan ("How to proceed further
with exchanging JML parsing").

## 2. Current state (as of this branch)

### 2.1 JML handling today

JML **syntax** is NOT parsed by KeY. JMLtk (used only as the Java parser) is
configured **without** JML processing, so it captures JML comments as opaque
`JmlDoc*` nodes; KeY then parses their text with its own ANTLR grammars:

```
key.core/src/main/antlr4/JmlLexer.g4      (JML tokens, comment modes, +KEY/+OPENJML/-KEY marker decision)
key.core/src/main/antlr4/JmlParser.g4     (spec_case, clause, expr, storeref, quantifiers, \by, \dl, assertionProof)
```
generated into `de.uka.ilkd.key.speclang.njml`.

### 2.2 Pipeline (data flow)

```
.java/.key source
  └─ JavaParserFactory / JavaService (JMLtk, processJml=OFF) ─ Java AST, JML captured as JmlDoc
      └─ KeYJavaPipeline (transformations)
          └─ JMLTransformer     ─ sanitizes JmlDoc text, calls PreParser,
                                  stores TextualJMLConstructs in JavaParser DataKeys
                                  (KEY_SPEC_CASE, KEY_CLASS_SPEC, KEY_LOOP_SPEC)
          └─ JmlDocRemoval      ─ strips JmlDoc nodes afterwards
      └─ JP2KeYConverter        ─ moves TextualJMLConstruct *into KeY AST* via
                                  attachedJml fields (declarations, classes, loops,
                                  blocks, MergePointStatement); JmlExpressionStmt → JmlAssert/SetStatement
  └─ SLEnvInput.read() → JMLSpecExtractor (SpecExtractor)
      └─ JMLSpecFactory         ─ builds Contract/ClassInvariant/ClassAxiom/InitiallyClause/
                                  LoopSpec/BlockContract/MergeContract/DependencyContract
                                  from TextualJML* via LabeledParserRuleContext
          └─ JmlIO → Translator → JmlTermFactory ─ JML parse trees → KeY terms (SLExpression/JTerm)
      └─ SpecificationRepository
```

Dotted boxes = the parts this rewrite removes/replaces.

### 2.3 Key classes to be retired / replaced

| Class(s) | Role | Fate |
|---|---|---|
| `speclang/jml/pretranslation/` — **all 17 classes** (TextualJMLConstruct, TextualJMLSpecCase, TextualJMLMethodDecl, TextualJMLClassInv, TextualJMLClassAxiom, TextualJMLInitially, TextualJMLRepresents, TextualJMLDepends, TextualJMLFieldDecl, TextualJMLLoopSpec, TextualJMLMergePointDecl, TextualJMLAssertStatement, TextualJMLSetStatement, TextualJMLModifierList, Behavior, JMLModifier) | intermediate "textual" JML representation | **deleted** — replaced by JMLtk AST |
| `speclang/njml/JmlLexer.g4`, `JmlParser.g4` | ANTLR JML grammar | **deleted** when unreferenced |
| `njml/PreParser` | text comment → TextualJMLConstruct | **deleted** (JMLtk parses) |
| `njml/TextualTranslator` | ANTLR visitor → TextualJML* | **deleted** |
| `njml/JmlFacade` | thin ANTLR facade (parseExpr/parseClause) | replaced by JMLtk `parseJmlExpression`/`parseJmlClause`/… |
| `njml/Translator` | ANTLR visitor → JTerm | **rewritten** as JML-AST → JTerm translator |
| `njml/JmlTermFactory` | JML ops → DL terms | **ported** into the new translator |
| `njml/LabeledParserRuleContext` | ANTLR context + TermLabel carrier | replaced by a light JML-AST + origin-label carrier |
| `njml/JmlMarkerDecision` | +KEY/+OPENJML marker policy | **kept**, but moves to `setJmlKeys()` config |
| `njml/JmlChecks`, `JmlCheck` | post-parse warnings | ported to JML-AST checks |
| `njml/SpecMathMode`, `OverloadedOperatorHandler`, LDT handlers | semantic helpers | **reused** by the new translator |
| `JMLSpecFactory` | JML → speclang factory | **rewritten** to consume `JmlContract`/`JmlClause`/`JmlClassLevelDeclaration` |

### 2.4 Classes kept as integration seams

`JMLSpecExtractor`, `SpecExtractor`, `SLEnvInput`, `SpecificationRepository`,
`JP2KeYConverter` (attachedJml transfer — payload changes to JML AST),
`JMLInfoExtractor`, `JMLResolverManager`, `JMLBuiltInPropertyResolver`,
`Context`, `ProgramVariableCollection` — plus the `speclang` root
(`Contract`, `ClassInvariant`, `ClassAxiom`, `InitiallyClause`,
`LoopSpecification`, impls) and `speclang/dl/DLSpecFactory` (`.key` DL specs).

## 3. JMLtk readiness (verified facts)

- JMLtk's `javaparser-core/src/main/javacc/java.jj` has contained full JML
  grammar productions since 2021 (`JmlContracts`, `JmlContractM`,
  `JmlContractClause`, `JmlLoopContract`, `JmlInvContract`, `JmlRefiningContract`,
  `JmlModelProgram`, contract clauses: requires/ensures/assignable/accessible/
  determined/measured_by/callable/signals/signals_only, …).
- **The published snapshot `io.github.jmltoolkit:jmlparser-core:3.28.2-J8.0-K13.5-SNAPSHOT`
  (mavenCentral + sonatype snapshots) DOES ship the generated JML grammar**
  (`JmlContractM`/`JmlContracts`/`JmlContractClause`/… present in
  `GeneratedJavaParser`), the `com.github.javaparser.jml.JmlProcessor`
  post-processor, and the parse entry points
  `JavaParser.parseJmlMethodLevel/ClassLevel/TypeLevel/ModifierLevel/Contract(s)/Clause/Expression`.
- JML processing is **off by default** and enabled via `ParserConfiguration`:
  - `parserConfiguration.setProcessJml(true)` — run `JmlProcessor`,
  - `setJmlKeys(List<List<String>>)` — marker key sets; `JmlProcessor` is
    re-run for every key set (this is where KeY's `+KEY`/`-KEY`/`+OPENJML`
    marker policy plugs in; default is `[[]]`, i.e. process all JML),
  - `setKeepJmlDocs(boolean)` — keep raw `JmlDoc` nodes after processing
    (warnings are reported for leftover docs when false).
- **Live verification with `setProcessJml(true)`** on the published jar:
  a class with `/*@ public normal_behavior … @*/` on a method and `//@ invariant`
  on a field parses to a real JML AST — `JmlContract` attached to the method
  (`MethodDeclaration.getContracts()`), children `JmlSimpleExprClause`
  (requires/ensures), `JmlMultiExprClause` (assignable), `JmlSignalsClause`
  (signals), and a `JmlClassExprDeclaration` for the class-level invariant.
  In-code JML statements (`JmlExpressionStmt`, `JmlGhostStmt`, `JmlLabelStmt`,
  `JmlRefiningStmt`) and lambda contracts are processed as well.
- JMLtk is **tested against JML harvested from KeY**: jmltk's
  `jmlparser-jml-tests` module (`FragmentTest`, `FullExamplesTest`,
  `JmlExpressionTest`, resolution tests, `fragments/` corpus) plus grammar
  commits titled "changes for KeY". KeY-side gap-fill should therefore be the
  exception, not the rule.
- **Per-construct mapping** (`TextualJML*` vs the `ast.jml`/`ast.key`
  replacement, clause-level mapping, verified gap list, integration notes):
  see `JML_MAPPING.md` on this branch.

> Correction note: an earlier version of this document claimed the published
> snapshot lacks the JML grammar. That was a false negative (a `strings` scan
> over the compressed zip) combined with the `setProcessJml(true)` option not
> being enabled in the probe. Neither issue exists; the option is the only
> missing piece from KeY's side.

## 4. Target architecture

```
.java (JML in comments)
  └─ JMLtk with setProcessJml(true) (+ setJmlKeys for KeY markers)
      └─ JmlProcessor attaches JmlContract / JmlClassLevelDeclaration /
          JmlExpressionStmt / … directly to the Java AST
      └─ KeYJavaPipeline
          └─ JMLTransformer (adapted or removed)  ─ no more PreParser/TextualJML*
          └─ JP2KeYConverter   ─ JML AST chunks attached to KeY AST (attachedJml)
  └─ SLEnvInput.read() → JMLSpecExtractor
      └─ JMLSpecFactory (rewritten) ─ consumes JmlContract/JmlClause/JmlClassLevelDeclaration
          └─ JML-AST Translator (new; replaces Translator+JmlTermFactory) → JTerm
      └─ SpecificationRepository
```

Design principles:

1. **JMLtk owns JML syntax.** KeY stops grammatically parsing JML. KeY's Java
   parser configuration enables `setProcessJml(true)`; JMLtk attaches
   `JmlContract` (method/loop/invariant), `JmlClause`, `JmlExpression` nodes to
   the declarations/statements they specify. Raw JML text stays recoverable for
   error messages via `JmlDoc`/`setKeepJmlDocs(true)`.
2. **Semantics stay in KeY.** KeY's `JMLSpecFactory` and a new JML-AST→`JTerm`
   translator implement KeY's interpretation of JML (spec math modes, LDT
   wiring, KeY extensions `\by`, backtick DL terms, `\dl_...`), mirrored from
   the current `Translator`/`JmlTermFactory`/`JMLSpecFactory`.
3. **No text round-trip.** `TextualJML*` disappears entirely; the only
   intermediate carrier is a thin wrapper pairing an `ast.jml` node with KeY
   origin labels/positions (replacing `LabeledParserRuleContext`).
4. **Tests are the contract.** The JML test suite below specifies "JML KeY
   supports". Parity = those tests pass against JML-AST-driven code. Where the
   AST makes semantics cleaner, tests may be adjusted only with recorded reason.

## 5. Phases

### Phase 0 — Enable & probe JMLtk JML parsing in KeY
Goal: JML parsed by JMLtk inside KeY's real pipeline, with a coverage report.
- Switch `JavaParserFactory` (and `JavaService`) to
  `new ParserConfiguration().setProcessJml(true)` with `setJmlKeys` reflecting
  KeY's default marker policy (`+KEY`/`+OPENJML` handling).
- Wire KeY's `+KEY`/`-KEY`/`+OPENJML` semantics onto `setJmlKeys`; verify
  behavior against `JmlMarkerDecisionTest`.
- Probe: parse the JML fixture corpus from the tests in §6 with the enabled
  config; compare which constructs yield clean `Jml*` AST vs. `JmlDoc` leftovers
  or parse problems. Report the gap list.
- Only gap-fill upstream (open jmltoolkit issues/PRs) for constructs KeY
  genuinely needs and JMLtk does not support yet.
- Deliverable: a mapping "JML construct → JMLtk AST node (or gap)" and a green
  `JavaParserFactory`-level smoke test.

### Phase 1 — Front-end swap on KeY side
- Replace the `TextualJML*` production: `JMLTransformer` no longer sanitizes
  JmlDoc text and calls `PreParser`; instead it (a) relies on the JML AST
  attached by `JmlProcessor`, and (b) only maps/validates it into KeY's
  `attachedJml`. `PreParser`, `TextualTranslator` and the DataKey storage of
  ANTLR contexts are deleted.
- Replace `LabeledParserRuleContext`/`TextualJML*` in `JP2KeYConverter`'s
  `attachedJml` with the JML-AST carrier (node + origin/position labels).
- `JMLSpecExtractor` unchanged in shape (reads attached JML); `JMLSpecFactory`
  input type swaps from `TextualJML*` to JML AST.

### Phase 2 — Semantic translation rewrite
- New `JMLSpecFactory` paths: `JmlContract` → `FunctionalOperationContract`,
  `BlockContract`, `LoopContract`, `MergeContract`, `DependencyContract`;
  `JmlClassLevelDeclaration` (invariant/represents/initially/model fields) →
  `ClassInvariant`, `ClassAxiom`/`Represents`, `InitiallyClause`, model/ghost
  field materialization.
- New translator walking `JmlExpression`/`JmlClause`/store-refs → `JTerm`/
  `LocationAccess`-sets, porting semantics from `Translator`/`JmlTermFactory`
  (operators via `OverloadedOperatorHandler`, quantifiers, `\old/_PRE`,
  `\result`, `\fresh`, `\typeof`, seq/map ops, `\seq_def`, math modes, JML
  built-ins, `\by`, backtick DL).
- Error reporting: keep message/position quality; map positions from JMLtk
  ranges back into the `.key`/`.java` file (reuse existing block-mapping logic).

### Phase 3 — Deletion & parity
- Delete the ANTLR grammars `JmlLexer.g4`/`JmlParser.g4` and the
  `speclang/njml` front-end classes (`PreParser`, `TextualTranslator`, legacy
  `Translator` paths) and the whole `speclang/jml/pretranslation` package.
- Update tests in §6 to the new pipeline; fix behaviors that legitimately
  change (recording reasons); keep the full `key.core`/`key.ui` run green on CI.
- Separate `.jml`/`.spec` files: parse via JMLtk (with which enclosing
  context?) or document the remaining gap.

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
`njml/exceptional/`). These fixtures double as the Phase 0 corpus probe input.

## 7. Open questions

1. Marker policy (`+KEY`/`-KEY`/`+OPENJML`): map onto `setJmlKeys()` semantics
   (JmlProcessor re-runs per key set). Verify equivalence with
   `JmlMarkerDecision`/`JmlMarkerDecisionTest`.
2. Attached-JML carrier: single `attachedJml` list of `ast.jml` nodes vs.
   typed slots per declaration kind.
3. `merge_point`: JMLtk only parses the raw-Java `merge_point ( expr );`
   (`ast.key.KeyMergePointStmt`); KeY writes `//@ merge_point …`. Decide:
   jmltk grammar change, or KeY-side normalization of the comment text.
4. Assert labels + proof scripts: JMLtk supports only JML-standard prefix
   labels (`//@ L1: assert e;`), not KeY's `assert LAB: e`, and has no
   `BY …` assertion-proof syntax. **Deferred: upstream JMLtk grammar support
   planned (near future); KeY keeps the raw `JmlDoc` text for these until
   then.**
5. Silent-mis-parse protection: `monitors_for`/`readable_if`/`writable_if`/
   `in_group`/`maps_into`/`nowarn`/`debug` tokens are absent from JMLtk and
   currently mis-parse (probe: `monitors_for` → spurious `JmlFieldDeclaration`).
   KeY must reject or pre-filter these.
6. `\strictly_nothing`, `\nothing`/`\everything` are plain `NameExpr`s in
   JMLtk — their locset meaning must be re-added in KeY's term translation.
7. Separate `.jml`/`.spec` files: parse via JMLtk with which enclosing context?
8. Position mapping: JMLtk `TokenRange` → KeY `Location` for warnings (Phase 2).
9. License header policy for new files on this branch (repo convention
   GPL-2.0-or-later vs current -only drift).
10. Performance: JMLtk parse time with JML processing on large files; and
    `JmlProcessor` behavior on `.key` files' embedded Java.

## 8. Immediate next step (after this doc)

Phase 0 spike — **no KeY code committed yet**:
1. Flip `setProcessJml(true)` (+ start mapping `setJmlKeys`) in a scratch
   `JavaParserFactory` change or standalone probe.
2. Run KeY's JML fixture corpus (§6) through it and report coverage: which
   constructs attach clean `Jml*` AST, which fall back to `JmlDoc` or produce
   problems.
3. Publish the gap list; only then decide on any jmltk upstream work.
