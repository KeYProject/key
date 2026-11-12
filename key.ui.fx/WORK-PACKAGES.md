# WORK-PACKAGES — finishing the Swing → JavaFX migration

Scope of this document: everything still open after the P0–P4 batches and the full merged-tree
sweep (Oct 11 2026, 34/34 PASS). Sources: `KNOWN-SIMPLIFIED.md` (43 OPEN markers),
`PARITY-SIGNOFF.md` (remaining-gaps rows), the deferred-integration and unverified-port lists in
the plan file (`~/.opencode/plan/key-ui-javafx-rewrite.md`).

## Global conventions (identical to the P-batches)

- One package = one branch `weigl/ocfx-wp<N>-<topic>`, one worktree, one agent; **agents push only
  their own branch**, the parent merges `--no-ff` into `weigl/ocfx` (never `main`, never
  `git add -A`).
- Gate every commit: `./gradlew --no-daemon :key.ui.fx:spotlessApply :key.ui.fx:compileJava
  :key.ui.fx:test` (plus the touched keyext module).
- Headless evidence on Xvnc (`DISPLAY=:99`), per-flag isolated app runs, sequential,
  `JAVA_TOOL_OPTIONS="-Xmx6g -Dprism.order=sw -Dkey.fx.verify.<flag>=1 [-Dkey.fx.demo.sequent=…]"`
  — new seams get new assertions inside the existing verify hook for their area, or a new
  `key.fx.verify.<name>` flag registered in `key.ui.fx/build.gradle` (run-task whitelist).
- Every package **updates the ledgers it touches**: `KNOWN-SIMPLIFIED.md` rows OPEN → RESOLVED
  (or WONT-REPLICATE with a one-line reason), `PARITY-SIGNOFF.md` rows, and the plan file.
- Memory discipline: one app run at a time, `--max-workers=1`; never edit a script while it runs.
- A trailing `BUILD FAILED`/exit-143 in a verify log is the runner's intentional pkill after the
  markers appear — expected.

## Package overview

| WP | Title | Depends on | Size | Ledger impact |
|----|-------|-----------|------|---------------|
| WP-1 | Mediator & shell seams (foundation) | — | M | key.ui.fx ×3 + unblocks 3 modules |
| WP-2 | Proof tree: heatmap overlay, branch editing, NodeInfo, click target | — | L | signoff prooftree row, KNOWN-SIMPLIFIED ×2 |
| WP-3 | Sequent/strategy/settings UI parity | — | M | signoff ×5 rows |
| WP-4 | Caching extension parity | WP-1 | S | KNOWN-SIMPLIFIED ×3 |
| WP-5 | Exploration extension parity | WP-1 | M | KNOWN-SIMPLIFIED ×7 |
| WP-6 | Slicing extension parity | — | M | KNOWN-SIMPLIFIED ×11 (+1 upstream decision) |
| WP-7 | TestGen + SMT dialogs & CE model view | WP-1 | L | KNOWN-SIMPLIFIED ×15 |
| WP-8 | Isabelle solver launch — port or close | — | S | KNOWN-SIMPLIFIED ×3 (decision) |
| WP-9 | Deferred integration wiring | — | M | signoff deferred rows |
| WP-10 | Unverified ports: verify & fix | — | S | signoff "OPEN (unverified)" rows |
| WP-11 | Endgame: FX default, final sweep, Swing retirement | WP-1…WP-10 | M | — |

Execution order: WP-1 first (everything parallelizable behind it), then WP-2/3/6/8/9/10 in
parallel, WP-4/5/7 after WP-1 lands, WP-11 strictly last.

---

## WP-1 — Mediator & shell seams (foundation) — `weigl/ocfx-wp1-mediator`

**Goal.** Add the `KeYMediatorF` seams four extension ports and the exit flow are missing, so
their KNOWN-SIMPLIFIED rows can be closed faithfully.

**Scope / sites.**
- `KeYMediatorF`: opened-proofs accessor (`getCurrentlyOpenedProofs` parity,
  Swing `KeYMediator.java`), extension-object register/lookup registry
  (`register(model, Class)` / lookup), GUI-listener registry + `fireShutDown`
  (Swing `GUIListener.shutDown`), auto-mode context API for foreign proofs
  (`initiateAutoMode`/`finishAutoMode` overload), proof-load listener registry.
- `MainWindowF.java:3721` — fire the shutdown event on exit through the new registry.
- `MainWindowF.java:2659` — glass-pane scope: either extend the freeze overlay to menu bar +
  toolbar + status bar (Swing parity) or close as WONT-REPLICATE with the disable-during-auto-mode
  argument written down. Decision belongs to this package.

**Deliverables.** Seams + wiring + unit tests (toolkit-free, like the existing ones).

**Acceptance evidence.** `key.fx.verify.extensions` extended with
register/lookup + opened-proofs assertions; `key.fx.verify.loadingexit` still exit-code=0;
`key.fx.verify.uicontrol` PASS. Ledger rows updated (caching 778, exploration 280,
MainWindowF:3721, MainWindowF:2659).

## WP-2 — Proof tree parity — `weigl/ocfx-wp2-prooftree`

**Goal.** Close the prooftree signoff row "heatmap/NodeInfoVisualizer/branch editing still OPEN".

**Scope / sites.**
- Heatmap proof-tree/sequent heat overlay (Swing `HeatmapExt` renderer; KNOWN-SIMPLIFIED
  `extension/contrib/HeatmapF.java:28` + `:37`) — port the renderer onto `ProofTreeViewF`
  (no Swing/AWT); demo flag + persisted settings already exist.
- Proof-tree branch editing (Swing tree interaction parity) — scoped per the plan's gap notes.
- NodeInfoVisualizer port (tooltip/label enrichment of nodes) or explicit WONT-REPLICATE.
- Tree popup click target: context menu acts on the **clicked** node, not the selection
  (signoff `OPEN (unverified)`) — fix + assert.

**Acceptance evidence.** `key.fx.verify.prooftree` extended (overlay visible on the demo,
branch-edit + click-target asserts); `key.fx.verify.heatmap` (new flag) rendering the overlay on
`strassen.auto.0.proof`; `key.fx.verify.rightclickmacro` still PASS.

## WP-3 — Sequent / strategy / settings UI parity — `weigl/ocfx-wp3-sequentui`

**Goal.** Close the five remaining sequent/goallist/settings signoff rows.

**Scope / sites.**
- Strategy preset combo + stash UI (goallist-strategy-info row, Swing strategy panel parity).
- Multi-selection highlight + reprint persistence (sequent row).
- View-menu **Pretty Print / Unicode** inert placeholders → real toggles (signoff row).
- Theme persistence (settings-config row: chosen theme survives restart).
- Parallel-prover status indicator: "SC"/"MT N×" button with worker-count menu
  (KNOWN-SIMPLIFIED `ParallelProverStatusIndicatorF.java:27`).

**Acceptance evidence.** `key.fx.verify.menuparity` extended (pretty-print/unicode toggles
wired); `key.fx.verify.sequent` multi-select assert; a restart round-trip assert for theme
persistence (settings save/load, headless); strategy preset combo asserted via
`key.fx.verify.goallist` extension.

## WP-4 — Caching extension parity — `weigl/ocfx-wp4-caching` *(after WP-1)*

**Scope / sites.**
- `CachingExtensionF.java:735` — port the interactive `ReferenceSearchDialog` (per-goal table +
  "Apply") as an FX dialog.
- `:778` — feed `mediator.getCurrentlyOpenedProofs()` (WP-1 seam).
- `CopyBeforeDisposeF.java:25` — wrap the copy into the WP-1 auto-mode context API.

**Acceptance evidence.** `key.fx.verify.extensions` extended with the reference-search dialog
render + apply-path assert (headless, no real slicing run needed); ledger ×3 rows closed.

## WP-5 — Exploration extension parity — `weigl/ocfx-wp5-exploration` *(after WP-1)*

**Scope / sites.**
- `ExplorationExtensionF.java:54/:280` — mediator register/lookup for `ExplorationModeModel`
  (WP-1 seam); `:76` restated row follows.
- Proof-tree renderer-styling hook on `ProofTreeViewF` (purple exploration border) +
  hidden second-branch filter (`:363` "Hide justification" → `HIDE_INTERACTIVE_GOALS` filter).
- `ExplorationSequentMenuF.java:48/:173/:182` — `promptForTerm` modal retry-loop until the term
  is well-typed (sort-mismatch re-prompt), replacing the single-shot abort.

**Acceptance evidence.** New `key.fx.verify.exploration` flag: model registered via mediator,
renderer border visible on a demo branch, retry-loop accepts then rejects a bad term; ledger
×7 rows closed.

## WP-6 — Slicing extension parity — `weigl/ocfx-wp6-slicing`

**Scope / sites.**
- Graphviz DOT rendering via a non-Swing path (FX `Image`/`ImageView` dialog or the existing
  browser seam) for `SlicingExtensionF.java:249` and `SlicingLeftPanelF.java:322/:618`
  (replaces DOT-as-text stand-ins).
- "Slice proof to fixed point" iterative dialog (`:222/:228`).
- HTML statistics with sortable columns + `HtmlFactory` timings (`:295`, `:464`) — use the
  `HelpFacadeF`/HTML-dialog seam instead of plain text.
- `:415` — load slices through the direct loader so they stay out of the recent-files list.
- `SlicingSettingsProviderF.java:29/:144` — **decision point**: the aggressive-deduplicate setter
  is package-private in `org.key_project.slicing`; either an upstream keyext change (separate
  approval) or close both rows WONT-REPLICATE with the constraint documented.

**Acceptance evidence.** New `key.fx.verify.slicing` flag: DOT renders as an image headless
(graphviz binary or fallback decision documented), fixed-point run on the gcd demo, HTML
statistics table rendered; ledger ×11 rows resolved/decided.

## WP-7 — TestGen + SMT dialogs & CE model view — `weigl/ocfx-wp7-testgen-smt` *(after WP-1)*

**Goal.** The biggest remaining cluster (15 markers): faithful run dialogs, progress/result
model views, and the extension SPI surfaces.

**Scope / sites.**
- `ToolbarF`/`StartupF` SPI: implement both capabilities (status-line toolbar slot already
  exists; window capture via `StartupF` hook) — `TestgenExtensionF.java:59/:72`, `:344`
  enabled-state updates via the action infrastructure.
- Macro keybinding slot: `SHORTCUT+T` on the TestGen strategy macro (`:193`) — either a
  `KeyStrokeSettings`-backed term-menu binding seam in key.ui.fx or a documented deviation.
- Auto-mode shell + cooperative stop: `TestgenReflectionF.java:160`,
  `TestGenerationTaskF.java:19` (WP-1 auto-mode context API; launcher-handle stop).
- Solver progress + results dialogs with the **counterexample model**:
  `TestgenReflectionF.java:220`, `CounterExampleTaskF.java:21`,
  `CounterExampleResultsDialogF.java:35/:131`, `TestGenResultsDialogF.java:43/:154`
  (embedded live options panel; window-from-start via StartupF).
- `InformationWindowF.java:24` — counterexample model tree (`CETree`) with line numbers + help
  tab in the Information window.
- `SolverListenerF.java:81` — apply results via an undoable user action with the input freeze
  (Swing `SMTProofApplyUserAction` parity); SMT per-solver settings panels (deferred row).

**Acceptance evidence.** `key.fx.verify.smt` extended (undoable apply assert); new
`key.fx.verify.testgen` flag: run dialog + progress + results dialog with a CE model rendered
headless (z3 at `/home/weigl/.local/bin/z3`); `key.fx.verify.extensions` still PASS;
ledger ×15 rows closed.

## WP-8 — Isabelle solver launch: port or close — `weigl/ocfx-wp8-isabelle`

**Scope.** `IsabelleTranslationExtensionF.java:37/:48`, `IsabelleTranslationRunnerF.java:28`.
Decision first: launching the real Isabelle backend (Scala, heavy, session-managed) headless is
high-cost/low-verification-value. Either (a) port `IsabelleLauncher` invocation with a progress
dialog on a background thread (translation-only stays as-is), or (b) close all three rows
WONT-REPLICATE with the backend-cost argument in the ledger. The translation feature itself
(theory generation + dialog) is already at parity.

**Acceptance evidence.** Ledger ×3 rows resolved with the decision recorded; if (a), a dry-run
progress-dialog assert without a real Isabelle installation.

## WP-9 — Deferred integration wiring — `weigl/ocfx-wp9-integration`

**Scope.** The verify hooks for AutoSave, Minimize-Interaction and EnsureSourceConsistency pass
in isolation, but their real-flow wiring is deferred:
- AutoSave: wire the saver into the proof lifecycle the way Swing arms it
  (`applyAutoSave` + load-success hand-off already exist — close the remaining gap and assert
  an actual timed save during an auto-mode run).
- Minimize-Interaction: wire into the load pipeline (settings → loading options → minimize mode).
- EnsureSourceConsistency: wire into the source view / symbex flow.
- Contract E2E: contract configurator → contract applied on the demo (dialogs verify covers the
  dialog surface only).

**Acceptance evidence.** `key.fx.verify.autosave` / `minimizeinteraction` extended to the real
flows; a contract E2E assert in `key.fx.verify.dialogs`.

## WP-10 — Unverified ports: verify & fix — `weigl/ocfx-wp10-unverified`

**Scope.** Ported-but-never-verified items from the signoff:
- Selection Back/Forward binding (View menu set).
- Apply-Strategy-at-node (tree popup) — overlaps WP-2's click-target work; verify first, fix if
  broken, coordinate scope with WP-2.
- Each item gets an explicit verify assertion; a failing port is fixed in this package.

**Acceptance evidence.** New asserts inside `key.fx.verify.menuparity` (back/forward) and
`key.fx.verify.rightclickmacro` (apply-strategy-at-node); signoff rows flip to RESOLVED.

## WP-11 — Endgame — `weigl/ocfx-wp11-endgame` *(strictly last)*

**Scope.**
1. Final full regression sweep: all previous flags **plus** every new flag introduced by
   WP-1…WP-10, per-flag isolated runs, sequential, on the fully merged tree (resume-safe runner
   conventions per the plan's incident notes).
2. **FX default switchover**: make `MainEx`/`:key.ui.fx:run` the documented default entry point
   (README, docs, launch scripts, demo configs); `-DmainClass` ergonomics reviewed.
3. **Swing retirement checklist** (not executed here): inventory of `key.ui` usages that
   `key.ui.fx` still compiles against, the `keyext.*` (Swing) counterparts, and a staged removal
   plan — each item as an explicit decision for the maintainers. The Swing UI keeps shipping
   until that decision is made.
4. Close `PARITY-SIGNOFF.md` (all rows RESOLVED/WONT-REPLICATE) and refresh the plan file's
   Status header.

**Acceptance evidence.** Sweep RESULTS with zero failed flags; docs updated; the retirement
checklist committed as part of this package.

---

## Decision points collected (need maintainer input, tracked per WP)

1. Glass-pane scope on freeze (WP-1): full-pane parity vs. views-only + documented deviation.
2. Aggressive-deduplicate setter (WP-6): upstream `keyext.slicing` change vs. WONT-REPLICATE.
3. Isabelle solver launch (WP-8): port vs. WONT-REPLICATE.
4. Swing retirement (WP-11): when and whether `key.ui` + `keyext.*` (Swing) are removed.
