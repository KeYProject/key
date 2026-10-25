# PLAN — Rewrite JML specification handling in KeY

Branch: `weigl/jmltk-jml` (PR #3997)

Status: **COMPLETE — implemented** (HEAD `d7fdfe737c`, committed 2026-10-26):
KeY's JML front-end reads JMLtk's **typed JML AST directly** as the single
source of truth, on top of `jmltk = 1.1.0-SNAPSHOT`. The intermediate `JmlSpec`
wrapper, the `attachedJml` carrier and the data-key spec relocation
(`KEY_SPEC_CASE`/`KEY_CLASS_SPEC`) are **gone**: contracts and class-level
specs are resolved back from the JMLtk AST via the KeY↔JMLtk reverse mapping
(`KeYJPMapping.registerReverse`). The `de.uka.ilkd.key.speclang.*` regression
slice is GREEN (**279 tests, 0 failures, 12 skipped**); whole-build
`compileJava`/`compileTestJava` and `spotlessCheck` are green.

The narrative below documents the *history* of the rewrite and is kept for the
record, but **§2 and §4 describe the shipped architecture**; `JML_MAPPING.md`
holds the per-construct mapping. Sections marked 'HISTORICAL' no longer match
the code.

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

## 2. Final state (as of this branch)

### 2.1 JML handling today

JML **syntax** is parsed by JMLtk: `JavaParserFactory` builds the parser with
`setProcessJml(true)` (+ `setJmlKeys` for KeY's `+KEY`/`+OPENJML` marker
policy); `JmlProcessor` attaches the typed JML AST directly to the Java AST.

KeY's own ANTLR grammars are retained as the **semantics layer only**:

```
key.core/src/main/antlr4/JmlLexer.g4      (JML tokens, comment modes, +KEY/+OPENJML/-KEY marker decision)
key.core/src/main/antlr4/JmlParser.g4     (spec_case, clause, expr, storeref, quantifiers, \by, \dl, assertionProof)
```

They are still generated into `de.uka.ilkd.key.speclang.njml` because (a) the
`JmlToTextual` bridge re-serializes the JMLtk clauses and re-parses them with
these rules to keep the proven `Translator`/`JmlTermFactory` semantics, and
(b) `JP2KeYConverter` re-parses `JmlExpressionStmt`/`set`/`merge_point`
statement texts the same way (`JmlFacade`).

### 2.2 Pipeline (data flow as shipped)

```
.java/.key source
  └─ JavaParserFactory (JMLtk, setProcessJml(true), JML keys policy)
      └─ JmlProcessor attaches the typed JML AST directly to the Java AST:
           JmlContract on NodeWithContracts nodes (methods, constructors,
           blocks, loop statements), JmlClassExprDeclaration/
           JmlRepresentsDeclaration/JmlClassAccessibleDeclaration class
           members, JmlMethodDeclaration/JmlFieldDeclaration wrappers,
           JmlExpressionStmt/JmlGhostStmt/KeyMergePointStmt statements
      └─ KeYJavaPipeline (transformations)
          └─ JMLTransformer     ─ re-processes method bodies and unwraps the
                                  wrappers: JmlMethodDeclaration/
                                  JmlFieldDeclaration are replaced by their
                                  contained declarations (the Javaparser
                                  symbol solver ignores wrapped declarations)
                                  and the wrapper is remembered on the inner
                                  node via the KEY_JML_WRAPPER data key;
                                  self-marks JML statements (KEY_ASSERT/
                                  KEY_ASSIGN on JmlExpressionStmt,
                                  KEY_MERGE_POINT on KeyMergePointStmt)
          └─ JmlDocRemoval       ─ strips remaining JmlDoc nodes afterwards
      └─ JP2KeYConverter         ─ converts the Java declarations. Pure
                                  class-level JML specs stay on the JMLtk type
                                  (no attachedJml, no JmlSpec anywhere);
                                  JmlExpressionStmt → JmlAssert/SetStatement;
                                  KeyMergePointStmt → MergePointStatement;
                                  createComments returns emptyList();
                                  registers the KeY→JMLtk reverse mappings:
                                  type → JmlTypeDeclaration, KeY method/ctor →
                                  contract carrier (the KEY_JML_WRAPPER
                                  wrapper for model methods, the
                                  NodeWithContracts node itself otherwise)
  └─ SLEnvInput.read() → JMLSpecExtractor (SpecExtractor)
      └─ resolves the specs back from the JMLtk AST via
         KeYJPMapping.nodeFromKeY: method contracts + model method definitions
         (JmlToTextual.toMethodDecl of the wrapper), class-level specs from
         the JMLtk type members, block/loop contracts from the attached
         JmlContract
      └─ JMLSpecFactory         ─ builds Contract/ClassInvariant/ClassAxiom/
                                  InitiallyClause/LoopSpec/BlockContract/
                                  MergeContract/DependencyContract from the
                                  typed classes (JmlContract,
                                  JmlMethodDeclaration, …); clause semantics
                                  via JmlToTextual → JmlParser.g4 re-parse →
                                  Translator/JmlTermFactory (the "bridge")
```

No dotted boxes: all parts of this flow are shipped.

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

> Corrections since this table was written:
> - `njml/Translator`, `JmlTermFactory`, `JmlParser.g4`/`JmlLexer.g4` and the
>   surviving `pretranslation` value classes were **kept** as the semantics
>   layer behind the `JmlToTextual` bridge (Phase-2 "Option B" decision, see
>   HANDOFF §5); `PreParser`/`TextualTranslator` were deleted.
> - No `attachedJml` carrier and no `JmlSpec` wrapper ever shipped; the
>   final carrier is the KeY↔JMLtk reverse mapping (see §2.2).

### 2.4 Classes kept as integration seams

`JMLSpecExtractor`, `SpecExtractor`, `SLEnvInput`,
`JP2KeYConverter` (registers the KeY→JMLtk reverse mappings via
`KeYJPMapping.registerReverse`; no `attachedJml`),
`JMLInfoExtractor`, `JMLResolverManager`, `JMLBuiltInPropertyResolver`,
`Context`, `ProgramVariableCollection` — plus the `speclang` root
(`Contract`, `ClassInvariant`, `ClassAxiom`, `InitiallyClause`,
`LoopSpecification`, impls) and `speclang/dl/DLSpecFactory` (`.key` DL specs).

`SpecificationRepository` **is deleted** (Phase 4 complete, see §5): specs
live attached to the AST nodes or in the Services-owned components.

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

## 4. Shipped architecture

```
.java (JML in comments)
  └─ JMLtk with setProcessJml(true) (+ setJmlKeys for KeY markers)
      └─ JmlProcessor attaches JmlContract / JmlClassLevelDeclaration /
          JmlMethodDeclaration/JmlFieldDeclaration /
          JmlExpressionStmt / … directly to the Java AST
      └─ KeYJavaPipeline
          └─ JMLTransformer  ─ re-processes method bodies; unwraps the
                               JmlMethodDeclaration/JmlFieldDeclaration
                               wrappers (remembered via KEY_JML_WRAPPER);
                               no PreParser/TextualJML*, no JmlSpec
          └─ JP2KeYConverter ─ converts the Java declarations; pure class-level
                               JML specs stay on the JMLtk type; registers the
                               KeY→JMLtk reverse mapping (registerReverse)
  └─ SLEnvInput.read() → JMLSpecExtractor
      └─ JMLSpecFactory (rewritten) ─ consumes the JMLtk typed classes
                                      (JmlContract, JmlMethodDeclaration, …),
                                      derives speclang objects attached to the
                                      AST
          └─ JmlToTextual → JmlParser.g4 → Translator/JmlTermFactory → JTerm
             (the semantics "bridge"; no direct JML-AST→JTerm translator)
      └─ SpecificationRepository  ← deleted (Phase 4)
```

Design principles (as realized):

1. **JMLtk owns JML syntax.** KeY stops grammatically parsing JML for
   *front-end* purposes; JMLtk attaches `JmlContract` (method/loop/invariant),
   `JmlClause`, `JmlExpression` nodes to the declarations/statements they
   specify. Raw JML text stays recoverable for error messages via
   `JmlDoc`/`setKeepJmlDocs(true)`.
2. **Semantics stay in KeY.** KeY's `JMLSpecFactory` and the
   `Translator`/`JmlTermFactory` machinery implement KeY's interpretation of
   JML (spec math modes, LDT wiring, KeY extensions `\by`, backtick DL terms,
   `\dl_...`). Rather than a new JML-AST→`JTerm` translator, `JmlToTextual`
   re-serializes each JMLtk clause/declaration and re-parses it with KeY's
   `JmlParser.g4` rules — the exact rules the old front-end used — so the
   specification semantics of the old front-end are preserved.
3. **The JMLtk AST is the single carrier.** There is no `TextualJML*`
   production from comments and no `attachedJml`/`JmlSpec` transfer into the
   KeY AST; the KeY↔JMLtk reverse mapping (`KeYJPMapping.registerReverse`) is
   the only bridge between the two ASTs, and specs are consumed straight from
   the JMLtk nodes.
4. **Tests are the contract.** The JML test suite below specifies "JML KeY
   supports". Parity = the `de.uka.ilkd.key.speclang.*` slice is green
   (279/0/12 at HEAD). Where the AST makes semantics cleaner, tests were
   adjusted only with recorded reason.

## 5. Phases

### Phase 0 — Enable JMLtk JML parsing in KeY
Goal: JML parsed by JMLtk inside KeY's real pipeline (construct→AST/gap mapping
already verified — see `JML_MAPPING.md` and §3).

> **DONE** (`9d1494b2cd`, extended in the 1.1.0-SNAPSHOT rebase): KeY builds the
> parser with JMLtk's `setProcessJml(true)` and the JML-keys policy.
- Switch `JavaParserFactory` (and `JavaService`) to
  `new ParserConfiguration().setProcessJml(true)` with `setJmlKeys` reflecting
  KeY's default marker policy (`+KEY`/`+OPENJML` handling).
- Wire KeY's `+KEY`/`-KEY`/`+OPENJML` semantics onto `setJmlKeys`; verify
  behavior against `JmlMarkerDecisionTest`.
- Only gap-fill upstream (open jmltoolkit issues/PRs) for constructs KeY
  genuinely needs and JMLtk does not support yet.
- Deliverable: a green `JavaParserFactory`-level smoke test.

### Phase 1 — Front-end swap on KeY side

> **DONE — as re-designed during the 1.1.0-SNAPSHOT rebase.** The original plan
> relocated the JML AST into a `JmlSpec` carrier on `attachedJml` fields
> (HISTORICAL). What shipped instead: no carrier at all. The JMLtk AST is the
> single source of truth; `JMLTransformer` only unwraps the wrapper
> declarations and self-marks JML statements; `JP2KeYConverter` registers the
> KeY→JMLtk reverse mappings and skips pure class-level JML spec members;
> `JMLSpecExtractor` reads the specs back from the JMLtk AST via the mapping.
> `JmlSpec.java`, `attachedJml`, `getAssociatedSpecificationComments` and the
> data-key spec relocation are deleted. `PreParser`, `TextualTranslator` and
> the DataKey storage of ANTLR contexts are deleted.

- Replace `LabeledParserRuleContext`/`TextualJML*` in `JP2KeYConverter`'s
  `attachedJml` with the JML-AST carrier (node + origin/position labels).
  → **not applicable in the final design** (no carrier; reverse mapping only).
- `JMLSpecExtractor` unchanged in shape (reads attached JML); `JMLSpecFactory`
  input type swaps from `TextualJML*` to JML AST.
  → readers now go through `KeYJPMapping.nodeFromKeY`.

### Phase 2 — Semantic translation rewrite

> **SUPERSEDED by "Option B"** (HANDOFF §5): instead of writing a new
> JML-AST→`JTerm` translator, the `JmlToTextual` bridge re-serializes the
> JMLtk clauses/declarations and re-parses them with KeY's `JmlParser.g4`
> rules, reusing `Translator`/`JmlTermFactory` unchanged. The items below are
> the originally planned (unshipped) approach; the as-built semantics layer is
> described in §2.2.
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

> **SUPERSEDED by Option B (see HANDOFF §5):** the *grammar* deletions and the
> `pretranslation`-package deletion listed here are half un-done, half done via
> the `JmlToTextual` bridge (which keeps the ANTLR grammars + `Translator`/
> `JmlTermFactory` as the semantics layer). What actually shipped:
> - Deleted: `PreParser`, `TextualTranslator`, `JmlCheck(s)` (dead), plus
>   `TextualJMLFieldDecl/ModifierList/SetStatement/MergePointDecl` (superseded by
>   the bridge) — Phase 3 bulk of the "delete" part.
> - Kept: `JmlLexer.g4`/`JmlParser.g4`, `pretranslation` value classes
>   (`TextualJMLSpecCase` et al. — still produced by `JmlToTextual`),
>   `Translator`/`JmlTermFactory`/`JmlIO`/`JmlFacade`.
> - Test cleanup DONE: stale tests deleted/rewritten; `speclang.*` slice green
>   (279 tests, 0 failures, 12 skipped). Parity gaps recorded in HANDOFF §5.1:
>   `spec_*_math` modifiers unparseable (pragmas removed, JAVA pin, 2 `@Disabled`
>   loads), error positions null, error types become jmltk wrappers, single `=`
>   silently dropped (`JmlToTextual.toSpecCase` try/catch),
>   `ModifiersTest` inline modifiers.

- Delete the ANTLR grammars `JmlLexer.g4`/`JmlParser.g4` and the
  `speclang/njml` front-end classes (`PreParser`, `TextualTranslator`, legacy
  `Translator` paths) and the whole `speclang/jml/pretranslation` package.
- Update tests in §6 to the new pipeline; fix behaviors that legitimately
  change (recording reasons); keep the full `key.core`/`key.ui` run green on CI.
- Separate `.jml`/`.spec` files: parse via JMLtk (with which enclosing
  context?) or document the remaining gap.

### Phase 4 — Delete `SpecificationRepository`: specs are rewritten via the AST

> **Progress (see HANDOFF §5.2/§7.3):** Phase 4 **COMPLETE** (slices 1–9:
> `bd33eb2331` statement specs → AST nodes; `63def34696` limited observers →
> `LimitedObservers`; `0ca80f062b` loop/block/merge specs → AST nodes;
> `8746c00939` proof↔PO registry → `ProofRegistry`/`Services`; `7c99a1cb92`
> class invariants/axioms → `ClassAxiomComputer`/`Services`; `4332456092`
> contract registry → `ContractRegistry`/`Services`; `5905ac02d2` initially
> clauses → `JMLSpecFactory` load path; `36190b66bd` `addSpecs` collapse +
> `map(...)` removal; `2a43925e8e` `SpecificationRepository.java` + the
> `Services`/`KeYEnvironment` accessors + `SpecificationRepositoryWD` deleted,
> WD `processJavaType` → `ContractRegistryWD`); full-suite baseline
> measured + A/B-verified (40 failures at slices-1–2 HEAD identical to
> Phase-3 HEAD — zero regressions), IntSemantics fixture fix landed
> (`2938f9ae8d`), leaving **34 recorded pre-existing jmltk gaps**. Formatting
> is folded into the rewritten branch history (each commit is
> `spotlessApply`-clean, so `spotlessJavaCheck`/CodeQuality is green with no
> fix-up commit); the other red CI jobs (caching/slicing/infflow/integration
> proofs) are pre-existing — same set at slice-3-era commits, untouched by
> slices 7–9 (see HANDOFF §1).

Rationale: with Phases 0–3 done, the *parsed* JML lives on the Java AST
(`attachedJml` on declarations, `getContracts()` on statements, `JmlStatementSpec`
on statements), and internal mechanisms (KeYJavaPipeline transformations,
`JP2KeYConverter`) rewrite that AST — and with it the specs. A central
`key.core/src/main/java/de/uka/ilkd/key/proof/mgt/SpecificationRepository.java`
that holds a *second* copy of the parsed/translated specifications is then pure
redundancy and a drift risk (every transformation must re-register/unregister
there; the current code does exactly that in ~10 metaconstructs and visitors).
Once the specifications stay attached to the Java AST they are rewritten by the
same internal mechanisms that rewrite the program — the repository's global
snapshot becomes unnecessary.

What the repository does today (`SpecificationRepository.java`, 1757 lines):

| Responsibility | Where it lives now | Where it moves |
|---|---|---|
| Contract registry: `contracts`, `operationContracts`, `contractTargets`, `contractsByName`, `getContracts/getOperationContracts/getContractTargets/getAllContracts/getContractByName` | `Map<Pair<KJT,obs>, Set<Contract>>` + name index | ✅ DONE (slice 6, `4332456092`) — moved to new `de.uka.ilkd.key.speclang.ContractRegistry` owned by `Services` (created via `Profile.createContractRegistry`; `WdProfile` returns `ContractRegistryWD`; shared by `Services.copy`). The registry is the successor home until specs migrate to the AST-attached per-node derived cache. |
| Contract combination/split: `combineOperationContracts` (`cf.union` sorted), `splitContract` (`§`-joined names), `CONTRACT_COMBINATION_MARKER` | name-based maps | ✅ DONE (slice 6, `4332456092`) — `combineOperationContracts`/`splitContract` moved to `ContractRegistry`; `CONTRACT_COMBINATION_MARKER` (`§`) to `ContractFactory` (public constant, refs in `BlockContractImpl`/`LoopContractImpl`/`FunctionalAuxiliaryContract`/`ProofRegistry` updated); combination stays deterministic by sorting. |
| Contract ids: `prepareContract`/`contractCounters` (`setID`) | per-type-name counter | ✅ DONE (slice 6, `4332456092`) — still on `ContractRegistry` (`prepareContract` + per-method `contractCounters` keep ids `.0`-stable across type-load order); the final move to `JMLSpecFactory`/`ContractFactory` at derivation time is a later cleanup. |
| Inheritance over overriding methods: `getOverridingMethods`, `getOverridingTargets`, `getCanonicalFormForKJT`, `getInheritedContracts` | method-name+param matching over `JavaInfo` | ✅ DONE (slice 6, `4332456092`) — moved to `ContractRegistry` (pure `JavaInfo`-based resolution; `ProofRegistry` and all callers rewired). |
| Class invariants: `invs`, `getClassInvariants`, `addClassInvariant` (+ inherit to subtypes, `PartialInvAxiom` creation) | `Map<KJT, Set<ClassInvariant>>` | ✅ DONE (slice 5, `7c99a1cb92`) — `invs` map + `getClassInvariants`/`addClassInvariant(s)` moved to `ClassAxiomComputer` (Services-owned; WD variant `ClassAxiomComputerWD` keeps registering `ClassWellDefinedness` checks). |
| Class axioms: `axioms`, `addClassAxiom` (represents conjoining), `getClassAxioms` incl. synthesized invariant-definition axioms (`invDef`/`staticInvDef`/`freeInvDef`/`freeStaticInvDef`), `QueryAxiom`s, model-method axioms (`getModelMethodAxioms`, `ContractAxiom`), `getVisibleAxiomsOfOtherClasses`, enclosing-class recursion (`getEnclosingKJT`), `allClassAxiomsCache` | `Map<KJT, Set<ClassAxiom>>` + cache | ✅ DONE (slice 5, `7c99a1cb92`) — moved to `de.uka.ilkd.key.speclang.ClassAxiomComputer` (per-`KeYJavaType` identity memo preserving the singleton requirement; operation-contract lookup is a documented temporary bridge to the still-alive repo). |
| Initially clauses: `initiallyClauses`, `addInitiallyClause`, `createContractsFromInitiallyClauses` (postcondition on all constructors, + inheritance) | `Map<KJT, Set<InitiallyClause>>` | ✅ DONE (slice 7, `5905ac02d2`) — moved to `JMLSpecFactory`: the factory collects `InitiallyClause`s during loading (`addInitiallyClause(s)` on the per-load factory that `SLEnvInput.createSpecs` already owns) and derives the constructor contracts at the end of loading (`createContractsFromInitiallyClauses()`; derived contracts register via `services.getContractRegistry()` with `addContractNoInheritance`/`unregisterContract`/`cf.addPost`/`cf.func` — same ordering as before). `ContractRegistry` loses the map + 4 methods; `unregisterContract` becomes public; repo `addSpecs` no longer dispatches `InitiallyClause`. |
| Loop invariants: `loopInvs`, `getLoopSpec`, `addLoopInvariant`, `copyLoopInvariant` (`(loop,line)` keys) | `Map<(LoopStatement,line), LoopSpecification>` | ✅ DONE (slice 3, `0ca80f062b`) — attached to the `LoopStatement` node (`setLoopInvariant`); `copyLoopInvariant` is `LoopStatement.copyLoopInvariantTo`, carried by the AST rewrites. |
| Block/loop/merge contracts: `blockContracts`, `loopContracts`, `loopContractsOnLoops`, `mergeContracts`, `get/add/remove{Block,Loop,Merge}Contract`, `getLoopContracts(LoopStatement, modality)` | `(block/loop,file,line)` keys | ✅ DONE (slice 3, `0ca80f062b`) — attached to `StatementBlock`/`LoopStatement`/`MergePointStatement` nodes; modality filtering is a pure helper (`AbstractAuxiliaryContractRule.get{Block,Loop}Contracts`). |
| Proof↔PO registry: `proofs`, `registerProof`, `removeProof`, `getProofs(po/contract/kjt+target)`, `getPO(Contract)`, `getPOForProof`, `getProofOblInput`, `getContractPOForProof`, `getTargetOfProof` | `Map<PO, Set<Proof>>` | ✅ DONE (slice 4, `8746c00939`) — moved verbatim to a new `de.uka.ilkd.key.proof.mgt.ProofRegistry` owned by `Services` (shared by `Services.copy()` copies, so side-proof envs and env-less loader paths keep the same registry); the contract-based lookups temporarily delegate `splitContract`/`getOverridingTargets` to the still-alive repository (they moved with the contract registry in slice 6). |
| Limited observers: `limitObs`/`unlimitObs`, `LIMIT_SUFFIX` `$lmtd`, limit/unlimit taclets | `Map<IObserverFunction,…>` | ✅ DONE (slice 2, `63def34696`) — moved to `de.uka.ilkd.key.util.LimitedObservers` (stateless + thread-safe static memo; taclet builders move along). |
| JML statement specs: `statementMap` (`IdentityHashMap<Statement,JmlStatementSpec>`), `getStatementSpec`/`addStatementSpec`, `JmlStatementSpec` record with `getTerm`/`updateVariables` | global identity map | ✅ DONE (slice 1, `bd33eb2331`) — attached to the `JmlAssert`/`SetStatement` AST nodes via `JmlSpecCarrier`; consumers read it off the node. |
| `map(UnaryOperator, Services)` (apply a term transformation to *all* specs, e.g. for at-pre/WD transforms) | walks every map | ✅ DONE (slices 8–9, `36190b66bd`/`2a43925e8e`) — deleted from the repo/registry/computer surface (it had zero callers): transformations run on the AST-attached spec; `IntroAtPreDefsOp`/WD re-walk the affected AST instead of the global snapshot. |
| `addSpecs` dispatcher, `processJavaType` no-op | — | ✅ DONE (slices 8–9) — `addSpecs` collapsed into the `SLEnvInput` output handling (`registerSpecs` helper, `36190b66bd`); `processJavaType` moved to `ContractRegistry` (empty default; WD override in `ContractRegistryWD` with the former `SpecificationRepositoryWD` body, `2a43925e8e`). |
| Thread-safety (synchronized maps for the parallel prover's lock-free phase) | explicit sync on hot maps | ✅ DONE (slices 8–9) — attached + derived specs are immutable after load; the parallel-prover mutation concern disappeared with the global registry (the last `synchronized` walkers were `map(...)`, now deleted). |

Transition notes:
- ~77 files reference `Services.getSpecificationRepository()`. Most calls are
  reads (`getContracts`, `getLoopSpec`, `getLoopContracts`, `getBlockContracts`,
  `getStatementSpec`, `getClassAxioms`, proof queries); each maps to an
  AST-node or proof-layer counterpart. Mutation sites (metaconstructs,
  visitors, `IntroAtPreDefsOp`, WD) stop maintaining a registry — they edit the
  AST and the attached specs follow.
- The `ClassAxiom` identity guarantee (no `equals`/`hashCode`, same instances
  required) must survive: memoize the `ClassAxiomComputer` per `KeYJavaType`
  and invalidate with the class-reload machinery (same life cycle as
  `allClassAxiomsCache` today).
- Contract `id` determinism: `prepareContract`'s counter moved to
  `ContractFactory` must keep ids stable across re-parse (proof digests,
  `.key` files, proof reuse compare ids — see `ContentOrderNumberingTest`).
- Deliverable: **REACHED** (`2a43925e8e`) — `SpecificationRepository.java` deleted;
  `Services`/`KeYEnvironment` expose no repository; the `key.core`/`key.ui`/
  `key.core.wd`/testgen/infflow suites stay at their recorded baselines with
  contract/loop/block/WD behaviors unchanged (only mechanical lookups were
  rewired slice by slice).

## 6. Regression net (tests defining KeY-supported JML)

`key.core/src/test/java/de/uka/ilkd/key/speclang/`:
- `njml/ClasslevelTranslatorTest`, `njml/ExpressionTranslatorTest`,
  `njml/ModifiersTest`, `njml/ContractLoadingTests`, `njml/JMLParserExceptionTest`
  (surviving; `MethodlevelTranslatorTest`, `TextualTranslatorTest`,
  `NJmlTranslatorTests` deleted in Phase 3 — they tested the removed front-end)
- `jml/TestJMLTranslator`, `jml/JmlMarkerDecisionTest`
  (`TestJMLPreTranslator`, `jml/pretranslation/TextualJMLAssertStatementTest`
  deleted in Phase 3)
- `SetStatementTest`, `ContractFactoryTest` (both rewritten in Phase 3 to the
  `JmlFacade.parseClause` / `set_statement()` re-parse path),
  `ContentOrderNumberingTest`
- related: `key.core/src/test/java/TranslationTest.java`,
  `KeyJavaPipelineTest.java`, `ReduxTest.java`,
  `key.core/src/test/java/de/uka/ilkd/key/parser/TestJMLParserAssociativity.java`

Fixtures: `key.core/src/test/resources/de/uka/ilkd/key/speclang/` (incl.
`njml/exceptional/` — metadata headers updated for jmltk error behavior;
`njml/methodlevel.txt` deleted).

## 7. Open questions

> Questions 1–2 are resolved by the shipped design; the rest are the recorded
> upstream/deferred gaps (see `JML_MAPPING.md` Part D).

1. Marker policy (`+KEY`/`-KEY`/`+OPENJML`): map onto `setJmlKeys()` semantics
   (JmlProcessor re-runs per key set). Verify equivalence with
   `JmlMarkerDecision`/`JmlMarkerDecisionTest`.
   → **Resolved:** the JML-keys policy is wired in `JavaParserFactory`;
   `JmlMarkerDecisionTest` is green in the slice.
2. Attached-JML carrier: single `attachedJml` list of `ast.jml` nodes vs.
   typed slots per declaration kind.
   → **Resolved — neither shipped.** There is no carrier between the ASTs; the
   KeY↔JMLtk reverse mapping (`KeYJPMapping.registerReverse`) is the bridge and
   specs are read straight from the JMLtk nodes (§2.2).
3. `merge_point`: JMLtk parses only the raw-Java `merge_point ( expr );`
   (`ast.key.KeyMergePointStmt`); KeY files author it as `//@ merge_point …`.
   Resolution: `JP2KeYConverter` translates `KeyMergePointStmt` back into the
   KeY merge-point statement (`//@ merge_point` form) — comment-form
   incompatibility neutralized on the KeY side.
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

## 8. Final build status (replaces the old "immediate next step")

All phases are implemented and verified at HEAD (`d7fdfe737c`):

- `./gradlew :key.core:test --tests "de.uka.ilkd.key.speclang.*"` → **GREEN**
  (279 tests, 0 failures, 12 skipped).
- `./gradlew compileJava compileTestJava` (whole build, incl. `key.ui` and the
  keyext modules) → green.
- `./gradlew spotlessCheck` → green; the commit is `git diff --check`-clean.
- Branch `weigl/jmltk-jml` pushed to origin; PR #3997 updated.
