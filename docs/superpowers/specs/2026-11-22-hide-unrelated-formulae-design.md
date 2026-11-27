# Hide formulae not transitively related to a term (KeYGuiExtension)

**Date:** 2026-11-22
**Status:** Approved by user (brainstorming)

## Goal

In the KeY sequent view, the user can click a *term* and, via the context menu, hide all
top-level sequent formulae that are not transitively related to that term **by syntax**.
Only the related formulae remain visible; the hidden ones are archived and can be restored
with KeY's built-in "Insert Hidden" mechanism.

## User flow

1. The user clicks a term in the goal sequent (`CurrentGoalView`) — the normal left-click
   context menu opens (it already lists "Copy to clipboard" and the extension section).
2. The user picks **"Show only formulas related to this term"** (new item contributed by the
   extension).
3. KeY computes the set of formulae syntactically related to the clicked term (see semantics)
   and applies the existing `hide_left` / `hide_right` rules to the currently selected goal
   for every formula *not* in that set.
4. The sequent now shows only the related formulae. Undo is the built-in mechanism:
   `hide_left` / `hide_right` auto-generate goal-local `insert_hidden` taclets, which KeY
   already exposes in the context menu under **"Insert Hidden"**.

## Semantics ("transitively related by syntax")

A formula *f* is transitively related to the clicked term *t* iff *f* is reachable from *t*
in the following bipartite graph:

- **Nodes:** all top-level sequent formulae (antecedent and succedent) and all distinct
  syntactic terms occurring in them.
- **Edge:** a formula node *f* is connected to a term node *s* iff *s* occurs verbatim as a
  subterm of *f* (structural `Term.equals`).

The **kept** set is the connected component containing the seed term *t*, intersected with
the formula nodes. Because edges propagate through shared subterms, chains of related
formulae are kept transitively, e.g. clicking `x` keeps all of
`x+1 = 0`, `x = y`, `y < 5` (each consecutive pair shares a subterm).

Properties of the definition:

- The clicked formula is always kept, because it contains *t* as a subterm.
- Term identity is structural `equals`. Alpha-renaming of bound variables is *not* matched
  in v1 (documented limitation).
- Occurrences inside `\program{...}` Java blocks are *not* considered (first-order subterms
  only; documented limitation).

## Core algorithm (pure, unit-testable)

```
input: Sequent goalSequent, Term seed

1. Build index: subterm s -> {formulae of goalSequent containing s}
   (subterm traversal of each formula via Term.subs()/execPostOrder)

2. BFS over term nodes, starting from `seed`:
     pop term s
     for each formula f with s in index[s]:
         if f not yet kept: add f to kept; enqueue every subterm of f
                             that has not been visited yet

output: kept formulae
```

Everything in `goalSequent` outside `kept` is hidden.

## Extension integration

- One new class in **key.ui**: `HideUnrelatedExtension`, implementing
  `KeYGuiExtension` + `KeYGuiExtension.ContextMenu` via `ContextMenuAdapter`,
  annotated `@KeYGuiExtension.Info(...)`, registered in key.ui's
  `META-INF/services/de.uka.ilkd.key.gui.extension.api.KeYGuiExtension` file
  (pattern: `SoundinessExtension`, `OriginTermLabelsExt`).
- `getContextActions` contributes one `KeyAction` only when:
  - `kind == ContextMenuKind.SEQUENT_VIEW`,
  - the `PosInSequent` has a real term position
    (`getPosInOccurrence() != null && posInTerm() != null`),
  - `mediator.getSelectedGoal() != null`.
  The action is disabled when nothing would be hidden (kept == all formulae) or when the
  clicked term does not resolve in the selected goal's sequent (e.g. a click in an
  inner-node view showing a different node — the feature targets the goal view).
- The action operates on `mediator.getSelectedGoal()`; the seed is the clicked
  `subTerm()` from the `PosInOccurrence`.
- Menu item name: **"Show only formulas related to this term"**.

### Resolution and guards

- The clicked formula is resolved in the goal sequent by comparing the clicked top-level
  formula with each goal formula (`TERM_LABELS_PROPERTY.equalsModThisProperty`, the same
  comparison `HideCommand` uses). If it is not found (e.g. click happened in an inner-node
  view showing a different sequent), **the action is disabled**.
- The resolved clicked formula is always added to the kept set (defensive; in the normal
  goal-view case it contains the seed already).
- If the kept set covers **all** goal formulae, the action is disabled ("nothing to hide").
- If the kept set would be empty (seed not present in the goal), the action is disabled as
  well — it must never hide all formulae.

## Hiding via existing rules (mirrors `SMTFocusResults.focus`)

For each goal formula *not* in `kept`:

- resolve the taclet `hide_left` (antecedent) / `hide_right` (succedent) via
  `goal.proof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(new Name(...))`;
- build a `PosTacletApp` with `MatchConditions` and
  `new PosInOccurrence(sf, PosInTerm.getTopLevel(), inAntec)`;
- instantiate the taclet's first schema variable with the whole formula
  (`app.addCheckedInstantiation(schema, (JTerm) sf.formula(), services, true)`);
- chain `goal = goal.apply(app).iterator().next();`.

If a taclet cannot be resolved or applying a rule fails, the action reports the failure
and stops (no partial state beyond already-applied hides, which is acceptable and visible
in the proof tree). The proof tree shows the chained hide steps; the GUI refreshes through
the existing proof-change listeners (same as SMT focus).

## Files

| File | Purpose |
| --- | --- |
| `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/HideUnrelatedExtension.java` | extension + `KeyAction` performing the hide |
| `key.ui/src/main/java/de/uka/ilkd/key/gui/extension/impl/RelatedFormulas.java` | pure component computation (subterm index + BFS) |
| `key.ui/src/main/resources/META-INF/services/de.uka.ilkd.key.gui.extension.api.KeYGuiExtension` | registration (one line) |
| `key.ui/src/test/java/de/uka/ilkd/key/gui/extension/impl/RelatedFormulasTest.java` | JUnit 5 unit tests for the component computation |
| `key.ui/src/test/java/de/uka/ilkd/key/gui/extension/impl/HideUnrelatedExtensionTest.java` | action enablement / resolution tests |

## Testing

- **Unit (component):** hand-built sequents covering:
  - direct occurrence of the seed in a formula,
  - chains through shared subterms (multi-hop),
  - unrelated formulae excluded,
  - seed with no occurrences anywhere (only the clicked formula kept),
  - duplicate subterm occurrences across formulae,
  - quantifier case (documents the alpha-renaming limitation).
- **Unit (action):** sequent/arrow click (no term position) → no item; no selected goal →
  disabled; everything related → disabled; clicked formula not present in the goal →
  disabled.
- **Manual GUI smoke test:** load a small proof with unrelated formulae, run the action,
  verify only related formulae remain and "Insert Hidden" restores them.

## Out of scope (v1)

- No alpha-renaming of bound variables in term matching.
- No occurrences inside `\program{...}`/Java-block code.
- Affects only the selected goal; other open goals are untouched.
- No new proof rules; reuse of `hide_left` / `hide_right` only.
