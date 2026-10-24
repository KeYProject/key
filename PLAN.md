# PLAN — Rewrite JML specification handling in KeY

Branch: `weigl/jmltk-jml` (created from `weigl/jmltk` @ `c91b316363`)
Status: **Phases 0+1 implemented** (HEAD `74b68f6f82`, `:key.core:compileJava`
GREEN) — KeY consumes JMLtk's parsed JML AST via `JmlSpec` wraps while keeping
KeY's translation semantics. **`HANDOFF.md` in the repo root is the current
checkpoint** (state, open Phase-2 decision, next actions). Approved direction:
remove KeY's own JML front-end and the `TextualJMLConstruct` intermediate
representation; use JMLtk's JML AST (`ast.jml`) directly.

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
  └─ JavaParserFactory (JMLtk, processJml=ON, JML keys policy) ─ Java AST with JML parsed
      by JmlProcessor and attached: JmlContract on declarations/statements (NodeWithContracts),
      JmlClassLevelDeclaration members, JmlExpressionStmt/JmlGhostStmt/KeyMergePointStmt in blocks
      └─ KeYJavaPipeline (transformations)
          └─ JMLTransformer     ─ relocates attached JmlContract/JmlClassLevelDeclaration into
                                  JmlSpec wraps on DataKeys (KEY_SPEC_CASE, KEY_CLASS_SPEC),
                                  unwraps JmlMethodDeclaration/JmlFieldDeclaration, self-marks
                                  JML statements (KEY_ASSERT/KEY_ASSIGN/KEY_MERGE_POINT)
          └─ JmlDocRemoval      ─ strips remaining JmlDoc nodes afterwards
      └─ JP2KeYConverter        ─ moves List<JmlSpec> *into KeY AST* via attachedJml fields
                                  (declarations, classes, loops, blocks, MergePointStatement);
                                  JmlExpressionStmt → JmlAssert/SetStatement; KeyMergePointStmt →
                                  MergePointStatement
  └─ SLEnvInput.read() → JMLSpecExtractor (SpecExtractor)
      └─ JMLSpecFactory         ─ builds Contract/ClassInvariant/ClassAxiom/InitiallyClause/
                                  LoopSpec/BlockContract/MergeContract/DependencyContract
                                  from JmlSpec (via JmlToTextual → TextualJML* → JmlParser.g4
                                  re-parse until Phase 2 lands a direct translator)
          └─ JmlIO → Translator → JmlTermFactory ─ JML parse trees → KeY terms (SLExpression/JTerm)
      └─ SpecificationRepository     ← Phase 4: deleted — specs stay attached to the AST
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

`JMLSpecExtractor`, `SpecExtractor`, `SLEnvInput`,
`JP2KeYConverter` (attachedJml transfer — payload changes to JML AST),
`JMLInfoExtractor`, `JMLResolverManager`, `JMLBuiltInPropertyResolver`,
`Context`, `ProgramVariableCollection` — plus the `speclang` root
(`Contract`, `ClassInvariant`, `ClassAxiom`, `InitiallyClause`,
`LoopSpecification`, impls) and `speclang/dl/DLSpecFactory` (`.key` DL specs).

`SpecificationRepository` is kept as a seam **only through Phase 3** and is
deleted in Phase 4 (specs then live attached to the AST / are derived per
node; see §5 Phase 4).

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
      └─ JMLSpecFactory (rewritten) ─ consumes JmlContract/JmlClause/JmlClassLevelDeclaration,
                                      derives speclang objects attached to the AST
          └─ JML-AST Translator (new; replaces Translator+JmlTermFactory) → JTerm
      └─ SpecificationRepository  ← Phase 4: removed (specs derived per AST node)
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

### Phase 0 — Enable JMLtk JML parsing in KeY
Goal: JML parsed by JMLtk inside KeY's real pipeline (construct→AST/gap mapping
already verified — see `JML_MAPPING.md` and §3).
- Switch `JavaParserFactory` (and `JavaService`) to
  `new ParserConfiguration().setProcessJml(true)` with `setJmlKeys` reflecting
  KeY's default marker policy (`+KEY`/`+OPENJML` handling).
- Wire KeY's `+KEY`/`-KEY`/`+OPENJML` semantics onto `setJmlKeys`; verify
  behavior against `JmlMarkerDecisionTest`.
- Only gap-fill upstream (open jmltoolkit issues/PRs) for constructs KeY
  genuinely needs and JMLtk does not support yet.
- Deliverable: a green `JavaParserFactory`-level smoke test.

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
| Contract registry: `contracts`, `operationContracts`, `contractTargets`, `contractsByName`, `getContracts/getOperationContracts/getContractTargets/getAllContracts/getContractByName` | `Map<Pair<KJT,obs>, Set<Contract>>` + name index | Contracts stay attached to the JML AST / KeY AST nodes (`MethodDeclaration.getContracts()` etc.) and are *derived* on demand by `JMLSpecFactory`; a per-node derived-spec cache replaces the global maps. Name→contract resolution moves to the `Contract` naming/keying layer (name is constructed from target + id). |
| Contract combination/split: `combineOperationContracts` (`cf.union` sorted), `splitContract` (`§`-joined names), `CONTRACT_COMBINATION_MARKER` | name-based maps | Pure computation on `ImmutableSet<FunctionalOperationContract>`; moves into `ContractFactory`/`Contract` (no repository state) — combination is already deterministic by sorting. |
| Contract ids: `prepareContract`/`contractCounters` (`setID`) | per-type-name counter | Id assignment moves to `JMLSpecFactory`/`ContractFactory` at derivation time (KeY already needs deterministic ids for `.key` I/O and digests). |
| Inheritance over overriding methods: `getOverridingMethods`, `getOverridingTargets`, `getCanonicalFormForKJT`, `getInheritedContracts` | method-name+param matching over `JavaInfo` | Pure `JavaInfo`-based resolution — moves to a helper next to `JMLSpecFactory`/`SLEnvInput` (or `JavaInfo` itself); no registry. |
| Class invariants: `invs`, `getClassInvariants`, `addClassInvariant` (+ inherit to subtypes, `PartialInvAxiom` creation) | `Map<KJT, Set<ClassInvariant>>` | Derived from `TypeDeclaration.attachedJml` invariant declarations; inheritance & `PartialInvAxiom` are derivation steps in `JMLSpecFactory`/`getClassAxioms` computation. |
| Class axioms: `axioms`, `addClassAxiom` (represents conjoining), `getClassAxioms` incl. synthesized invariant-definition axioms (`invDef`/`staticInvDef`/`freeInvDef`/`freeStaticInvDef`), `QueryAxiom`s, model-method axioms (`getModelMethodAxioms`, `ContractAxiom`), `getVisibleAxiomsOfOtherClasses`, enclosing-class recursion (`getEnclosingKJT`), `allClassAxiomsCache` | `Map<KJT, Set<ClassAxiom>>` + cache | All synthesizable axioms are pure functions of (JavaInfo, invariants, contracts, represents); the `getClassAxioms(kjt)` computation moves to `JMLSpecExtractor`/a `ClassAxiomComputer` with a per-`KeYJavaType` memo (preserving the singleton identity requirement `equals`/`hashCode` rely on). |
| Initially clauses: `initiallyClauses`, `addInitiallyClause`, `createContractsFromInitiallyClauses` (postcondition on all constructors, + inheritance) | `Map<KJT, Set<InitiallyClause>>` | Derivation step in `JMLSpecFactory` (initially → constructor postconditions) run at load time from `attachedJml` — no repository. |
| Loop invariants: `loopInvs`, `getLoopSpec`, `addLoopInvariant`, `copyLoopInvariant` (`(loop,line)` keys) | `Map<(LoopStatement,line), LoopSpecification>` | Attached to the `LoopStatement` AST node already in Phase 1; `copyLoopInvariant` (used by `InnerBreakAndContinueReplacer` etc.) becomes copying the attached spec to the new loop — the AST rewrites carry it. |
| Block/loop/merge contracts: `blockContracts`, `loopContracts`, `loopContractsOnLoops`, `mergeContracts`, `get/add/remove{Block,Loop,Merge}Contract`, `getLoopContracts(LoopStatement, modality)` | `(block/loop,file,line)` keys | Attached to `StatementBlock`/`LoopStatement`/`MergePointStatement` AST nodes; modality filtering stays as a pure helper on the contract set. |
| Proof↔PO registry: `proofs`, `registerProof`, `removeProof`, `getProofs(po/contract/kjt+target)`, `getPO(Contract)`, `getPOForProof`, `getProofOblInput`, `getContractPOForProof`, `getTargetOfProof` | `Map<PO, Set<Proof>>` | Proof-lifecycle bookkeeping is orthogonal to JML; moves to the proof management layer (`ProofEnvironment`/`ProofCorrectnessMgt`), which already own the lifecycle — a local `Map<PO, Set<Proof>>` there, or derive via `PO.getProofs()`. |
| Limited observers: `limitObs`/`unlimitObs`, `LIMIT_SUFFIX` `$lmtd`, limit/unlimit taclets | `Map<IObserverFunction,…>` | Taclet *construction* moves to `Ramification`/the rule that needs them (`TacletGenerator`); the maps become stateless functions (limited-name is a pure function of the observer), so no repository needed. |
| JML statement specs: `statementMap` (`IdentityHashMap<Statement,JmlStatementSpec>`), `getStatementSpec`/`addStatementSpec`, `JmlStatementSpec` record with `getTerm`/`updateVariables` | global identity map | Attached to the `JmlAssert`/`SetStatement` AST nodes (Phase 2 already produces the `JmlStatementSpec`); lookups via the node — consumers (`JmlAssertRule`, `SetStatementRule`, `IntroAtPreDefsOp`, `PrettyPrinter`, `MiscTools`) read it off the node. |
| `map(UnaryOperator, Services)` (apply a term transformation to *all* specs, e.g. for at-pre/WD transforms) | walks every map | Becomes the *reason* the rewrite is safe to delete: transformations run on the AST-attached spec; `IntroAtPreDefsOp`/WD re-walk the affected AST instead of the global snapshot. |
| `addSpecs` dispatcher, `processJavaType` no-op | — | `addSpecs` collapses into `JMLSpecFactory` output handling; `processJavaType` (empty) disappears. |
| Thread-safety (synchronized maps for the parallel prover's lock-free phase) | explicit sync on hot maps | Attached + derived specs are immutable after load; the parallel-prover mutation concern disappears with the global registry. |

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
- Deliverable: `SpecificationRepository.java` deleted; `Services`/`KeYEnvironment`
  expose no repository; the whole `key.core`/`key.ui` test suite green with
  contract/loop/block/WD behaviors unchanged (fix only mechanical lookups).

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

1. Marker policy (`+KEY`/`-KEY`/`+OPENJML`): map onto `setJmlKeys()` semantics
   (JmlProcessor re-runs per key set). Verify equivalence with
   `JmlMarkerDecision`/`JmlMarkerDecisionTest`.
2. Attached-JML carrier: single `attachedJml` list of `ast.jml` nodes vs.
   typed slots per declaration kind.
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

## 8. Immediate next step (after this doc)

Phase 0 spike — **no KeY code committed yet**:
1. Flip `setProcessJml(true)` (+ start mapping `setJmlKeys`) in a scratch
   `JavaParserFactory` change or standalone probe.
   (A corpus coverage report and gap publication are intentionally *not* part
   of the spike: the mapping and gap list are already established in
   `JML_MAPPING.md`/§3, and upstream work is decided on demand.)
