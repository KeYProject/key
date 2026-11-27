# Hide Unrelated Formulas Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a SequentView context-menu action — "Show only formulas related to this term" — that hides every formula of the selected goal not transitively related (by shared syntactic subterms) to the clicked term, using the existing `hide_left`/`hide_right` proof rules.

**Architecture:** A pure, GUI-free relevance computation in key.core (`RelatedFormulas`) computes the kept formula set; a thin KeYGuiExtension in key.ui (`HideUnrelatedExtension` + `KeyAction`) resolves the clicked term against the selected goal, disables itself when there is nothing to hide, and applies `hide_left`/`hide_right` rule apps to each unrelated formula (pattern: `SMTFocusResults.focus`). Undo is KeY's built-in "Insert Hidden" (`insert_hidden` taclets that the hide rules generate goal-locally).

**Tech Stack:** Java 21, Gradle multi-module (key.core, key.ui), Swing (`JMenu`/`KeyAction`), ServiceLoader-based KeYGuiExtension discovery, JUnit 5 (Jupiter), AssertJ allowed, JSpecify nullness annotations, Spotless.

**Spec:** `docs/superpowers/specs/2026-11-22-hide-unrelated-formulae-design.md`

## Global Constraints

- Only modify central modules `key.core` and `key.ui`; never add a `keyext.*` dependency to them.
- New public code in key.core/key.ui keeps the existing package schemes (`de.uka.ilkd.key.*`); Javadoc on public classes and public methods (short, self-explanatory).
- Use slf4j `LOGGER` constants; never write to `System.out`/`System.err`.
- Use JSpecify `@Nullable`/`@NonNull` annotations where the codebase does.
- JUnit 5 (Jupiter); AssertJ allowed; no `@Tag("owntest"/"interactive"/"performance")`.
- Run `./gradlew spotlessApply` on changed files before committing; no single-purpose spotless commits.
- Commit locally and regularly; do not push, do not open PRs (unless the user asks).
- Term identity means structural `Term.equals` (bound-variable alpha-renaming is deliberately NOT matched — documented limitation).

## Review Focus

Input classes/failure modes the spec implies but no single task fully exercises — every line is pinned to a test in the list below:

1. **Click on a formula-level position** (`PosInSequent` with `posInOccurrence() == null` or `posInTerm() == null`): no context-menu item at all and no NPE. → key.ui contract test.
2. **Click in a view whose formula is not part of the selected goal** (e.g. an inner-node view of a different node): the action must be disabled, not silently hide everything. → key.core test (`computeKeptFormulas` returns `Optional.empty()` when the clicked formula is absent from the sequent).
3. **Seed term occurs only inside the clicked formula**: only that formula is kept; the action stays enabled (there is something to hide). → key.core test.
4. **Everything is already related**: the action is disabled ("nothing to hide"), and the menu item never hides *all* formulae. → key.core test via the named `hidesNothing` predicate.
5. **Alpha-variant bound variables** (e.g. `∀x.P(x)` vs `∀y.P(y)` built with fresh `LogicVariable`s): NOT connected (structural equality only) — behavior documented by a test asserting non-connection.

---

### Task 1: Pure relevance computation in key.core

**Files:**
- Create: `key.core/src/main/java/de/uka/ilkd/key/logic/RelatedFormulas.java`
- Test: `key.core/src/test/java/de/uka/ilkd/key/logic/RelatedFormulasTest.java`

**Interfaces:**
- Produces (consumed by Task 2):
  - `de.uka.ilkd.key.logic.RelatedFormulas.computeKeptFormulas(Sequent sequent, JTerm seed, SequentFormula clickedFormula) : Optional<Set<SequentFormula>>`
    — `Optional.empty()` iff no formula of `sequent` matches `clickedFormula` (matching formula terms by `TERM_LABELS_PROPERTY.equalsModThisProperty`, the same comparison `de.uka.ilkd.key.scripts.HideCommand.find` uses). Otherwise the transitive-component set: all formulae reachable from `seed` in the bipartite graph (formula f — term s iff s is a subterm of f), with `clickedFormula` always included. Never returns an empty set (the clicked formula contains the seed, so it is in its own component).
  - `RelatedFormulas.hidesNothing(Sequent sequent, Set<SequentFormula> kept) : boolean`
    — true iff `kept.size() >= sequent.size()` (used by the action to disable itself).
- Imports it uses (verify against existing API; all exist today):
  - `org.key_project.prover.sequent.{Sequent, Semisequent, SequentFormula}` (iteration via `sequent.antecedent()`/`succedent()`, both `Iterable<SequentFormula>`).
  - `org.key_project.logic.{Term, Visitor}`, `de.uka.ilkd.key.logic.JTerm` (`execPostOrder(Visitor<JTerm>)` yields every subterm incl. the root).
  - `de.uka.ilkd.key.logic.equality.TermLabelsProperty.TERM_LABELS_PROPERTY`.

- [ ] **Step 1: Write the failing test**

Add a test base: build raw `TermImpl` terms (no `Services` needed — same approach `TestTermFactory.testSimplePredicate` uses) plus `TacletForTests.services().getTermBuilder()` (`TermBuilder`) where convenient, wrap in `new SequentFormula(j)`, assemble with `JavaDLSequentKit.createSequent(ImmutableList<SequentFormula>, ImmutableList<SequentFormula>)`.

Include at least these tests (AssertJ `assertThat`):
1. `directAndSharingFormulasAreKept`: sequent `p(x,y)`, `q(x)`, `unrelated` `r(u)` (no shared subterm); seed = the `x` of the first formula; expect kept = {`p(x,y)`, `q(x)`}.
2. `chainIsTransitive`: `p(x,y)`, `q(y,z)`, `r(z)`, `s(u)`; seed = `x` from `p(x,y)`; expect kept = all except `s(u)` (2-hop chain through shared variables).
3. `seedInsideClickedFormulaOnly`: clicked formula `P(x)` (seed `x` elsewhere absent), plus `Q(a)`; expect kept = {`P(x)`} and `hidesNothing` == false.
4. `clickedFormulaAbsentYieldsEmpty`: `computeKeptFormulas(sequentWithoutF, seed, f)` returns `Optional.empty()`.
5. `allRelatedIsNothingToHide`: one formula containing the seed; expect `kept` == the single formula and `RelatedFormulas.hidesNothing(sequent)` == true.
6. `duplicateSharedSubtermConnects`: `p(x,y)` and `p(x,z)` (same `x` term object in both) — both kept via the single `x` node; plus a formula `r(u)` excluded.
7. `alphaVariantBoundVarNotConnected`: `∀x.P(x)` and `∀y.P(y)` with distinct `LogicVariable`s `x`,`y`; seed = first formula's formula body (`P(x)`); expect the second formula is NOT kept (documents the structural-equality limitation).

- [ ] **Step 2: Run the test to verify it fails**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.logic.RelatedFormulasTest"`
Expected: FAIL — `RelatedFormulas` does not exist yet.

- [ ] **Step 3: Implement `RelatedFormulas` in `key.core/src/main/java/de/uka/ilkd/key/logic/RelatedFormulas.java`**

Public final utility class, private ctor. Two public static methods whose signatures are above. Algorithm for `computeKeptFormulas`:
1. Locate the clicked formula's match in `sequent`: iterate `sequent.antecedent()` then `succedent()`, return `Optional.empty()` if no formula term satisfies `TERM_LABELS_PROPERTY.equalsModThisProperty(goalTerm, clickedTerm)`.
2. Build `index`: for every formula `f` of the sequent, for every subterm `s` of `f` collected via `execPostOrder`, add `f` to `index.computeIfAbsent(s, ...)` (a `Map<Term, Set<SequentFormula>>`; `Term` has structural `equals`/`hashCode`).
3. BFS from `seed` over terms: `visited` terms (start `{seed}`), queue `[seed]`; pop `s`, for each `f ∈ index[s]` not yet kept: add `f` to kept and enqueue every subterm of `f` not visited yet.
4. Always `add(clickedFormula)` to kept (defensive; normally already present).

`hidesNothing`: `return kept.size() >= sequent.size();`

Note: do NOT traverse Java blocks inside modality terms (out of scope v1).

- [ ] **Step 4: Run the test to verify it passes**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.logic.RelatedFormulasTest"`
Expected: PASS (all listed tests green).

- [ ] **Step 5: Run spotless and commit**

Run: `./gradlew spotlessApply`
Expected: formatting applied, no errors.

```bash
git add key.core/src/main/java/de/uka/ilkd/key/logic/RelatedFormulas.java key.core/src/test/java/de/uka/ilkd/key/logic/RelatedFormulasTest.java
git commit -m "Add RelatedFormulas: compute formulae transitively related to a term"
```

---

### Task 2: KeYGuiExtension + hide action in key.ui

**Files:**
- Create: `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/HideUnrelatedExtension.java`
- Modify: `key.ui/src/main/resources/META-INF/services/de.uka.ilkd.key.gui.extension.api.KeYGuiExtension` (append one class name)
- Test: `key.ui/src/test/java/de/uka/ilkd/key/gui/extension/impl/HideUnrelatedExtensionTest.java`

**Interfaces:**
- Consumes: `RelatedFormulas.computeKeptFormulas(Sequent, JTerm, SequentFormula)` and `RelatedFormulas.hidesNothing(Sequent, Set<SequentFormula>)` from Task 1 (exact signatures above).
- Produces: the registered extension + its `KeyAction`.

- [ ] **Step 1: Write the failing test**

`HideUnrelatedExtensionTest` (plain JUnit 5, no term infrastructure needed — all inputs are null/arrow positions):
1. `noItemsForNonSequentKinds`: `extension.getContextActions(null, ContextMenuKind.PROOF_TREE, null)` is empty; same for `INFO_TREE`.
2. `noItemsForEmptySequentPosition`: `extension.getContextActions(null, ContextMenuKind.SEQUENT_VIEW, PosInSequent.createSequentPos())` is empty (arrow position has no `PosInOccurrence`).
3. `actionDisabledWhenNothingToHideOrNoGoal`: for a `PosInSequent` whose `PosInOccurrence` has a null-able guard path — assert that a `PosInSequent` with `posInOccurrence() == null` yields no item, and that the extension never throws NPE for any of these inputs.

- [ ] **Step 2: Run the test to verify it fails**

Run: `./gradlew :key.ui:test --tests "de.uka.ilkd.key.gui.extension.impl.HideUnrelatedExtensionTest"`
Expected: FAIL — class does not exist.

- [ ] **Step 3: Implement `HideUnrelatedExtension` in `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/HideUnrelatedExtension.java`**

- `@KeYGuiExtension.Info(name = "Hide Unrelated Formulas", description = "...", experimental = true, optional = true, priority = 100)` on the class; implement `KeYGuiExtension` + `KeYGuiExtension.ContextMenu` (delegate to a `ContextMenuAdapter`, see `SlicingExtension` for the idiom).
- `getContextActions(mediator, kind, object)` returns `List.of()` when any of:
  - `kind != ContextMenuKind.SEQUENT_VIEW`,
  - `object` is not a `PosInSequent`,
  - `pos.getPosInOccurrence() == null` or `pos.getPosInOccurrence().posInTerm() == null`,
  - `mediator == null || mediator.getSelectedGoal() == null`.
  Otherwise return `List.of(new HideUnrelatedAction(mediator, goal, pos.getPosInOccurrence()))`.
- Inner class `HideUnrelatedAction extends de.uka.ilkd.key.gui.actions.KeyAction`:
  - Constructor: `setName("Show only formulas related to this term")`; compute the plan once:
    `RelatedFormulas.computeKeptFormulas(goal.sequent(), (JTerm) pio.subTerm(), pio.sequentFormula())`;
    `setEnabled(plan.isPresent() && !RelatedFormulas.hidesNothing(goal.sequent(), plan.get()))`.
  - `actionPerformed`: recompute the plan; if empty, return (should be unreachable — the item is disabled). Otherwise for every formula of `goal.sequent()` not in `kept`:
    - antecedent → `hide_left`, succedent → `hide_right`, exactly the `SMTFocusResults.focus` mechanics: `PosTacletApp.createPosTacletApp(hideTaclet, new MatchConditions(), new PosInOccurrence(sf, PosInTerm.getTopLevel(), inAntec), goal.proof().getServices())`, instantiate the first schema var with `sf.formula()` via `app.addCheckedInstantiation(var, (JTerm) sf.formula(), services, true)`, then chain `current = current.apply(app).iterator().next()`.
    - Taclets via `goal.proof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name("hide_left"))` / `("hide_right")`; if either resolves to `null`, `setEnabled(false)` at construction (they always resolve for JavaDL).
  - After chaining: if `mediator.getSelectedNode() == goal.node()` then `mediator.getSelectionModel().setSelectedNode(current.node())` so the sequent view refreshes (pattern: `SolverListener.focusResults`).

- [ ] **Step 4: Register the extension**

Append the line `de.uka.ilkd.key.gui.extension.impl.HideUnrelatedExtension` to the services file `key.ui/src/main/resources/META-INF/services/de.uka.ilkd.key.gui.extension.api.KeYGuiExtension`.

- [ ] **Step 5: Run the test to verify it passes**

Run: `./gradlew :key.ui:test --tests "de.uka.ilkd.key.gui.extension.impl.HideUnrelatedExtensionTest"`
Expected: PASS.

- [ ] **Step 6: Compile the whole UI module (ensures the SMT-focus imports resolve)**

Run: `./gradlew :key.ui:compileJava`
Expected: BUILD SUCCESSFUL.

- [ ] **Step 7: Run spotless and commit**

Run: `./gradlew spotlessApply`
Expected: formatting applied, no errors.

```bash
git add key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/HideUnrelatedExtension.java key.ui/src/main/resources/META-INF/services/de.uka.ilkd.key.gui.extension.api.KeYGuiExtension key.ui/src/test/java/de/uka/ilkd/key/gui/extension/impl/HideUnrelatedExtensionTest.java
git commit -m "Add HideUnrelatedExtension: hide formulae not related to a term"
```

---

### Task 3: Whole-branch verification

**Files:**
- None (verification only), unless a task failure surfaces a fix.

- [ ] **Step 1: Run both new test suites**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.logic.RelatedFormulasTest" :key.ui:test --tests "de.uka.ilkd.key.gui.extension.impl.HideUnrelatedExtensionTest"`
Expected: both PASS.

- [ ] **Step 2: Format check and full compile of affected modules**

Run: `./gradlew spotlessCheck && ./gradlew testClasses`
Expected: `spotlessCheck` clean; `testClasses` BUILD SUCCESSFUL.

- [ ] **Step 3: Nullness check on the touched modules** (Checker Framework gate, per AGENTS.md)

Run: `./gradlew -DENABLE_NULLNESS=true :key.core:compileTestJava :key.ui:compileTestJava`
Expected: BUILD SUCCESSFUL (no nullness findings in the new files).

- [ ] **Step 4: Manual GUI smoke test** (requires `./gradlew key.ui:run` with a proof loaded)

1. Load a small JavaDL proof (e.g. any of `key.ui/examples`), left-click a term that occurs in several formulas plus unrelated ones → context menu shows **"Show only formulas related to this term"**.
2. Click it → only transitively related formulas remain in the sequent; the proof tree shows the chained `hide_left`/`hide_right` steps; unrelated formulas gone.
3. Right-click to re-open the menu → "Insert Hidden" lists the hidden formulas; inserting restores them.
4. Click a formula-level/arrow position → the item is absent. Click a term in an inner-node view of a different node → the item is present but disabled (greyed out).
5. With everything related to the clicked term → item disabled.

Expected: all five behaviors as described; no exceptions in the log.

- [ ] **Step 5: Commit any fixes found during verification**

```bash
git add -A
git commit -m "fix: address verification findings for hide-unrelated-formulas"
```

---

## Self-Review Notes

- **Spec coverage:** component semantics → Task 1 tests 1–3/6; resolution guards + never-hide-everything → Task 1 tests 4–5, Task 2 test 3; hide via `hide_left`/`hide_right` + undo via `insert_hidden` → Task 2 step 3, Task 3 step 4; context-menu integration + key.ui placement → Task 2; alpha-renaming + Java-block exclusions → Task 1 test 7 + step 3 note.
- **Type consistency:** `computeKeptFormulas`/`hidesNothing` signatures spelled identically in Task 1 Interfaces and Task 2 Consumes.
- **Review Focus:** all five lines pinned to concrete tests (see Review Focus section).
