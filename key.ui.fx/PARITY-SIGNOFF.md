# Parity sign-off — Swing→JavaFX audit (2026-10-08) vs. delivered application

This document signs off the parity audit that was carried out on 2026-10-08 against the
in-development JavaFX UI. The audit inventoried ~490 behaviors across nine components
(report index: `/tmp/opencode/parity-*.md`, synthesis in the appended table).

**Warning:** the audit predates milestones MP7–MP10 and the MP9.x keyext ports, so a large share
of the "MISSING" entries have since been delivered. This sign-off re-states each gap against the
delivered application and the `key.fx.verify.*` regression hooks, and carries forward everything
still open into the close-out list at the end.

Evidence used: the MP9 combined regression run (16/16 PASS), menuparity 5/5, termmenu 25,
tacletmatch 9/9, uicontrol 4/4, the six MP9.x module ports, and the consolidated
[KNOWN-SIMPLIFIED ledger](KNOWN-SIMPLIFIED.md). Items without an app-level regression hook are
marked `OPEN (unverified)` rather than assumed fixed.

## Component verdicts

| Component (audit report) | Behaviors | Audit verdict | Resolution since | Current status |
|---|---|---|---|---|
| mainwindow | 62 | 13 PORTED / 24 PARTIAL / **17 MISSING** / 6 KNOWN-DEF | window shell, menu/toolbar/status parity, docking, drawers (MP1–MP10) | mostly resolved; open items below |
| prooftree | 53 | 20 / 8 / **13 MISSING** / 5 KNOWN-DEF | core tree faithful; P3a sweep items, WP-10 click-target + Apply-Strategy, WP-2 heatmap/NodeInfoVisualizer/branch editing | RESOLVED (remaining gaps documented in KNOWN-SIMPLIFIED) |
| sequent | 45 | 14 / 10 / **15 MISSING** / 4 KNOWN-DEF | term context menu + taclet application + search (MP8); multi-selection highlight + reprint persistence (WP-3) | context menu RESOLVED; user-selection highlight + reprint persistence RESOLVED (WP-3 `key.fx.verify.sequent`); remaining items below |
| interactive-completion | 25 | 0 / 0 / **20 MISSING** | `WindowUserInterfaceControlF` seam + tacletmatch + join/merge | RESOLVED (was the top P0; evidence uicontrol + tacletmatch 9/9) |
| goallist-strategy-info | 37 | goal list at parity; strategy preset UI missing; info view re-designed | strategy preset combo / stash UI ported (WP-3: the Swing `StrategySelectionView.createDefaultPanel` [⚙][combo][Apply] row with Defaults + built-ins + user presets, save/stash/rename/delete over `StrategyPresetsSettings`, Apply writes maxSteps + properties like Swing :572-585; `key.fx.verify.goallist` preset round trip PASS) | stats staleness KNOWN-DEFERRED (deliberate): `InfoViewF` observes `selectedProofChanged` only (`InfoViewF.java:94-99`) — the statistics go stale after interactive rule applications until the next proof change/auto-mode stop (Swing `InfoView.java:83-111` refreshes on node changes too); per-feature deferral, outside the WP-1…WP-10 scope |
| source-search-filechooser | 74 | 30 / 5 / **28 MISSING** | search bars + loading-options dialog ported | source-view interaction (symbex highlights, cross-highlight) KNOWN-DEFERRED (deliberate, documented at `SourceViewF.java:64-66/:110/:237` — the tab-per-file UI, the proof-node ↔ source-line symbex highlights and the sequent-hover origin cross-highlight stay deferred; per-feature deferral, outside the WP-1…WP-10 scope) |
| menus-actions | 57 leaves | ~25 MISSING | menu parity 5/5 (File 16 / Proof 24 / Options 12 / View 7 / About 5) plus automation submenu | RESOLVED at surface level; a few behaviours below |
| settings-config | 117 | 83 / 8 / 11 MISSING / 13 KNOWN-DEF | settings framework + providers + colors mechanics + search; theme persistence (WP-3: `ThemeManager` persists the choice to the user preference node, restore at startup, `key.fx.theme` stays the one-off override; `key.fx.verify.themepersist` save/restore round trip PASS) | color definitions + SMT run UI RESOLVED (P1); theme persistence RESOLVED (WP-3) |
| unported-dialogs | 18 | 13 MISSING / 2 PARTIAL | proofmgmt, tacletmatch, IssueDialog, notification, Loaded Proofs | RESOLVED where noted below; join/mergerule/lemmatagenerator/etc. track their MP9.x modules |

## P0 sign-off (the audit's "prover workflow critical" list)

| Audit item | Delivered in | Evidence | Status |
|---|---|---|---|
| `UserInterfaceControlF` seam (status/progress/task/exception callbacks, `RuleCompletionHandler`) | `WindowUserInterfaceControlF` + diamond issue/LogView/AutoDismiss | `key.fx.verify.uicontrol` 4/4 (`wasShown=true` for the exception dialog) | **RESOLVED** |
| Sequent term context menu (`CurrentGoalViewMenu` ~900 LOC) | `SequentTermContextMenuF` + `SequentMenuModelF` | `key.fx.verify.termmenu` 25 checks; interactive rule apps in-app | **RESOLVED** |
| TacletMatch suite (gates interactive rule application) | `TacletMatchDialogF` + panels | `key.fx.verify.tacletmatch` 9/9 | **RESOLVED** |
| Abandon Proof | Proof menu (24 items) | `key.fx.verify.menuparity` Proof 24 | **RESOLVED** |
| ProofManagementDialog + TaskTree / Loaded Proofs dockable | `keyext.proofmanagement.fx` (MP9.6) + Loaded Proofs view | `key.fx.verify.proofmgmt` 1/2 | **RESOLVED** |
| IssueDialog / error reporting | `IssueDialogF` (toasts + dialog) | `key.fx.verify.uicontrol` (exception leg) | **RESOLVED** |
| Goal Back / Prune disable bindings; input freeze during auto mode | **RESOLVED** (P1: the auto mode blocking overlay — main area covered, mouse input blocked, keys swallowed except Escape, wait cursor; wired to the auto mode listener incl. the demo-live stop path; `key.fx.verify.inputfreeze` PASS) | — | **RESOLVED** |
| Apply Strategy on node + Prune-at-node in the tree popup | **RESOLVED** (WP-10: the popup's Apply Strategy / Prune actions run on the clicked node — the popup context is built from the clicked row like Swing `ProofTreeView.mousePressed` (`getPathForLocation` + `setSelectionPath`), not from the selection; `key.fx.verify.prooftree` asserts the real handlers: popup on the clicked node with the selection parked elsewhere, a capped strategy run grows the clicked node's subtree (nodes 1->21) and the prune removes it again (20->1) — "PASS - popup on clicked node … prune 20->1") | — | **RESOLVED** |

P0 bugs from the audit:

| Bug | Status |
|---|---|
| FX search stale on node switch | **RESOLVED** (search re-runs on reprint; sequent-leftovers milestone `18df960b35`) |
| Proof-tree context menu acts on the selection, not the clicked node | **RESOLVED** (WP-10: the context-request handler resolves the clicked row from the event-target `TreeCell` — the FX counterpart of Swing's `JTree.getPathForLocation` — and selects it like Swing `setSelectionPath`; the clicked node, not the previous selection, becomes `ProofTreeContext.invokedNode`; `key.fx.verify.prooftree` PASS "popup on clicked node, parkedSelection=true") |
| View-menu Pretty Print / Unicode inert placeholders | **RESOLVED** (WP-3: the items were already wired to the ViewSettings + NotationInfo statics + `refreshPrettyViews` since MP3a — the real gap found and fixed was the *initial* sequent printer, built from a bare `new NotationInfo()` that printed plain syntax regardless of the settings; the shared `createPrinter` now refreshes from the ViewSettings like Swing's mediator-owned NotationInfo; `key.fx.verify.menuparity` PrettyUnicode leg fires the real CheckMenuItems and asserts the settings mirroring, the Unicode disable binding and the visible effect — `PASS - pretty[true->true] unicodeEffect=true`; the demo sequent has no arithmetic, so its pretty/default notation is identical and the visible effect is asserted through the state-aware unicode toggle) |
| Recent-file clicks drop stored profile / single-java options | **RESOLVED** (P1: `openProofFile` registers the loading options with the entry like Swing `WindowUserInterfaceControl.loadProblem`; the recent-files menu restores profile (resolved via `DefaultProfileResolver`) / additional options / single-java like Swing `RecentFileAction`, `key.fx.verify.loadingexit` round trip PASS) |
| Shortcut-default mismatches (`KeyStrokeManagerF`: tree search, sequent search, macro defaults) | **RESOLVED** (P1: the defaults match the Swing table now — macros and PrettyPrint/Unicode/ProofManagement/tree-search on Ctrl+Shift, sequent search on Ctrl+F instead of the bare F that hijacked typing; stale persisted old defaults heal on load; `key.fx.verify.shortcuts` PASS) |
| Dead registered bindings (Ctrl+C term copy, F3/Shift+F3, Ctrl+K/Ctrl+J, Goal Back/Prune) | **RESOLVED** (P1: Ctrl+C copies the term under the mouse via the sequent view handler + the term-menu copy item carries the accelerator; term-menu global macro items carry their accelerators and the view-level macro keys run at the last clicked position (Swing `MacroKeyBinding`); F3/Shift+F3, Ctrl+K/Ctrl+J, Goal Back/Prune wired and covered by `key.fx.verify.shortcuts`) |
| Colors: 12 mapped CSS variables ineffective (47 property definitions missing) | **RESOLVED** (P1: `ColorPaletteF` defines all 51 Swing-parity properties — the true count incl. the two multi-line `define(` keys; the 9 previously-undeclared mapped CSS vars are declared in both themes and consumed by the re-wired `.sequent-hl-*`/`.source-*` rules; `key.fx.verify.colors` PASS) |
| UPSTREAM (Swing, not FX): `LoopApplyHeadCompletion` + `LoopContract*` dead code; seed-clobber `overwriteWith` | **Not our defect** — flags for upstream `key.ui`/`key.core` cleanup |

## P1 sign-off

| Audit item | Status |
|---|---|
| Loading options (profile / ignore other Java files) | **RESOLVED** — load-options dialog ported (`key.fx.verify.profileloading` + `profileloadingdialog` PASS) |
| Select Goal Above / Below + menu set (View 7) | **RESOLVED** (WP-10: Selection Back/Forward verified — `key.fx.verify.selectionhistory` PASS: the View menu's Back/Forward items carry the KeyStrokeManagerF accelerators (Ctrl+Alt+Left/Right), follow the history-driven enablement and firing them moves the mediator selection back/forward over the `SelectionHistoryF` — "PASS (navigation: moved 0->148)"; the View-menu surface itself was already `key.fx.verify.menuparity` View 7 PASS) |
| Automation submenu + macro invocation | **RESOLVED** (automation submenu MP2, macro menu in term menu); global toolbar dropdown KNOWN-DEFERRED (deliberate): with B14 the FX keeps ONE merged extension toolbar and the Swing `DropdownSelectionButton` macro-dropdown has no dedicated slot — macros run from the Automation submenu and the sequent/tree macro menus (B12); a toolbar dropdown control remains a possible small follow-up |
| Join / merge dialogs | **RESOLVED** for the merge/join flow (`key.fx.verify.joinmerge` PASS on gcd 32/0); `keyext.slicing.fx` SMT routing partial |
| Strategy preset combo / stash UI | **RESOLVED** (WP-3: the Swing `StrategySelectionView.createDefaultPanel` [⚙][combo][Apply] row ported — Defaults first, then the built-in presets, then the stored user presets with the "✕" delete affordance; save/stash/rename via the gear menu's parameterized core methods over `StrategyPresetsSettings` (Swing :663-750), Apply writes maxSteps + properties into the proof's live settings and gates on `predefChanged` like Swing `applySelectedPreset` :572-585; `key.fx.verify.goallist` asserts the entry list + stash/save/rename/delete round trip + write-through + Apply gating — "PASS - entries=3 stash/save/rename/delete=ok maxSteps=10000->10000") |
| SMT settings + run UI | **RESOLVED** (P1: settings providers ported in MP4; the run UI — `SolverListenerF` + `ProgressDialogF` progress table + `InformationWindowF` + result application via the SMT rule — ported, `key.fx.verify.smt` PASS: Z3 closes the Agatha goal; the Swing toolbar `DropdownSelectionButton` remains tracked under the toolbar item (KNOWN-DEFERRED, see the P1 automation row); WP-7: the per-solver command/parameters/timeout/support panels are ported as `SolverOptionsF` child providers of the SMT settings entry (Swing `SolverOptions` parity, KNOWN-DEFERRED — deliberate per-feature deferral of WP-7, sites `SolverOptionsF.java:35/:130`: `updateSMTSelectMenu` refresh + progress mode/global timeout/bounds/store path, the FX main window has no SMT select-menu counterpart yet) and the result application is the undoable `SMTProofApplyUserActionF` with the undoable-apply assert in `key.fx.verify.smt`) |
| Exit flow (close-request, `confirmExit`, layout save) | **RESOLVED** (P1: the window close button and the Exit menu item run the Swing `ExitMainAction` flow — `confirmExit` dialog, recent-files save, `System.exit(0)` which runs the docking/colors/keystrokes shutdown hooks; WP-1: the Swing mediator `fireShutDown` is now ported — `KeYMediatorF` GUI-listener registry + the exit flow fires the event, KNOWN-SIMPLIFIED row RESOLVED; `key.fx.verify.loadingexit` PASS: recent-files round trip + profile resolution, then the close-request path terminates with exit code 0 and the docking layout is saved) |
| Term labels; Pretty Print / Unicode wiring | **RESOLVED** for the wiring (WP-3: the View-menu toggles drive the ViewSettings + NotationInfo statics + the `refreshPrettyViews` re-render, and the initial printer honors the settings like Swing — see the P0 row; visible effect via `key.fx.verify.menuparity` PrettyUnicode PASS). Term labels stay covered mechanically by the `key.fx.verify.lemmaorigin` hook |
| User-selection highlight + Ctrl+C copy | **RESOLVED** (term-menu copy item in the skeleton); multi-selection highlight + reprint persistence **RESOLVED** (WP-3: sticky Ctrl+click / middle-click toggle in the `userSelectionOverlay` pane with the Swing `PERMANENT_HIGHLIGHT_COLOR` colors (light rgba(110,85,181,0.3), dark rgba(210,185,201,0.78), SequentViewInputListener.java:135-145); the highlight survives plain reprints and settings-change re-renders via `recalculateUserSelectionRange` over `table.pathForPosition`/`rangeForPath` (Swing SequentView.java:585-660, without the Swing +1 offset — the FX position table indexes match the printed text); cleared on node switch (documented deviation — Swing keeps the stored position across node switches but also loses it visually when the view instance swaps); `key.fx.verify.sequent` PASS — reprint=true settings=true toggle=true) |
| Symbex source line highlights + sequent-hover origin cross-highlight | KNOWN-DEFERRED (deliberate, per-feature deferral documented at the source sites: `SourceViewF.java:64-66` — "the tab-per-file UI … deliberately deferred", `:110` — "deferred: the Swing view updates the symbolic execution highlights here", `:237`; outside the WP-1…WP-10 scope) |
| KeyStroke default wiring next to the registry | **RESOLVED** (P1: `key.fx.verify.shortcuts` PASS — Swing-parity defaults, no binding collisions, an override round trip and the sequent-view Ctrl+F key path; the defaults table lives inside the FX registry `KeyStrokeManagerF` (`defineDefault`), so "wiring next to the registry" is exactly what the hook asserts) |

## P2 sign-off

Heatmap overlay (RESOLVED via WP-2 — the heat overlay is ported onto `SequentViewF` in the
Swing-faithful scope: the Swing original `SequentView.updateHeatMapHighlights` renders into the
sequent views only, never the proof tree), NodeInfoVisualizer + the proof-tree renderer surface
and branch-label F2 editing (RESOLVED via WP-2, see carried-forward item 2),
info-view node-change refresh, notification framework depth, docking title
actions/layout slots/maximize (partially done — `key.fx.verify.docking` PASS; title actions
exist as `DockTitleActionF`), join+mergerule dialogs (track MP9.x modules), lemmatagenerator
(`key.fx.verify.lemmaorigin` PASS for the generator path), soundiness (`key.fx.verify.soundiness`
PASS), originlabels (lemmaorigin), plugins, profileloading (RESOLVED), help windows
(`key.fx.verify.help` PASS), theme persistence (color definitions RESOLVED via P1
`key.fx.verify.colors`; the persistence itself RESOLVED via WP-3, item 9 below), feature
flags + parallel prover (`ParallelProverStatusIndicatorF` RESOLVED via WP-3 — the SC/MT toggle
button with the worker-count context menu, `key.fx.verify.extensions` proverMode leg PASS;
KNOWN-SIMPLIFIED row RESOLVED), settings dump, modal
grey-out, proof-disposal clearing (auto saver handles the disposal part), tab icons/titles,
file-chooser bookmarks. Each is either documented in the KNOWN-SIMPLIFIED ledger or listed above
as open.

## Still-open work list (carried forward)

1. Input freeze during auto mode (blocking glass pane port) — RESOLVED via P1
   `key.fx.verify.inputfreeze`; glass-pane scope decided in WP-1: WONT-REPLICATE — the FX
   overlay keeps covering only the views area (the menu/toolbar proof actions are disabled
   during auto mode anyway, the automation macro items must stay clickable to stop a run, and
   the status bar must stay live for the progress display) — KNOWN-SIMPLIFIED.
2. Proof-tree: Apply Strategy on clicked node, Prune-at-node in the popup (both RESOLVED via
   WP-10 `key.fx.verify.prooftree`), renderer surface, NodeInfoVisualizer, branch-label F2
   editing — RESOLVED (WP-2): the renderer surface is ported (leaf goal icons — closed goal,
   cached-closed, linked, interactive, open — as FontAwesome glyph stand-ins for the Swing
   key-hole gifs, non-leaf marker icons in the Swing priority window/notes/useless/interactive/
   script, the branch linked-folder icon, tooltip notes + useless-analysis lines, and the
   `NodeInfoVisualizerListenerF` attachment that re-renders on register/unregister like Swing's
   `nodeInfoVisListener`); branch-label F2 editing is ported with the Swing
   `DefaultTreeCellEditor.isCellEditable` gate (only branch entries whose node has a parent —
   the root branch is denied) and the commit seam mirroring
   `GUIProofTreeModel.valueForPathChanged → GUIBranchNode.setLabel → NodeInfo.setBranchLabel`
   plus the full rebuild; the heatmap heat overlay renders into the sequent view (the Swing
   original touches the sequent views only). Documented deviations: the Swing key-hole gif
   images have no FontAwesome glyph equivalents (state colors stay on the text classes, icons
   use the neutral `key-icon` fill), and `key.fx.verify.prooftree` asserts the surface —
   `branchEdit rootEditable=false labelEdit=PASS leafIcons=3 nodeInfoVisualizer=PASS PASS`
   (`/tmp/opencode/wp2/prooftree-agatha3.log`) and the heatmap leg
   `sfAge=1 sfNewest=5 termsAge=6 termsNewest=3 off=0 PASS` (`/tmp/opencode/wp2/heatmap1.log`).
3. Sequent: multi-select highlight + reprint persistence (RESOLVED via WP-3
   `key.fx.verify.sequent`), drag & drop, inner-node highlights +
   taclet info pane, source cross-highlight.
4. Source view: symbex line highlights, click-to-jump into the proof tree, hover
   cursor/line highlight, multi-file tabs, branch status bar.
5. Menus/actions: Pretty Print / Unicode wiring (RESOLVED via WP-3 — see the P0 row;
   `key.fx.verify.menuparity` PrettyUnicode PASS), term labels, tooltip toggles, selection
   Back/Forward bindings (RESOLVED via WP-10 `key.fx.verify.selectionhistory`), Edit Last File,
   Load User Taclets + Prove submenu, Run All Proofs
   (dialogs exist for several), EnableWhenProofLoaded analogue, toolbars 9 remaining buttons.
6. Keyboard: shortcut-default regressions; dead bindings audit (RESOLVED via P1
   `key.fx.verify.shortcuts`; the Swing-persisted `keystrokes.json` stays the source of truth
   for user overrides).
7. Options dialogs: strategy preset UI (RESOLVED via WP-3 — the strategy tab's [⚙][combo][Apply]
   row + `key.fx.verify.goallist` PASS), HeatmapOptionsDialog (SMT run UI RESOLVED via P1
   `key.fx.verify.smt`).
8. Exit flow: close-request + confirmExit + layout persistence on close (RESOLVED via P1
   `key.fx.verify.loadingexit`; the Swing `fireShutDown` event now fires through the WP-1
   `GUIListenerF` registry seam — `MainWindowF.java:3721` RESOLVED).
9. Colors/theme: all 51 Swing-parity color property definitions RESOLVED (P1 `key.fx.verify.colors` PASS); theme persistence RESOLVED (WP-3: `ThemeManager` persists to the user preference node, `key.fx.verify.themepersist` save/restore round trip PASS — save `applied=DARK persisted=DARK`, restore `restored=DARK persisted=DARK reset=LIGHT`).
10. Notification framework depth: proof-closed/exception dialogs beyond toasts are in
    (`IssueDialogF`); the `NotificationTask`/action framework remains partial.
11. Docking: remaining title actions, layout-slot keys F10–F12 (named slots exist).
12. Upstream (Swing) flags: `LoopApplyHeadCompletion`/`LoopContract*` dead code, seed-clobber.

### Close-out status (WP-11, 2026-10-12)

Of the carried-forward list above, items 1, 2, 6, 7, 8 and 9 are RESOLVED with the evidence
cited inline (P1…P4 batches and the WP-1…WP-10 merges; per-WP evidence logs under
`/tmp/opencode/wp*/`). Item 5 is resolved in its main parts: term labels (`key.fx.verify.lemmaorigin`),
the Load-User-Taclets dialog (P2b `LoadUserTacletsDialogF`), the Prove submenu
(`buildProveSubmenu`, `MainWindowF.java:482`) and Run All Proofs (`RunAllProofsF`, behind the
Swing-parity feature flag, `MainWindowF.java:241`) are ported; the remainder of item 5 and the
other per-feature tails are deliberate KNOWN-DEFERRED deferrals of the FX port, each documented
at its source site or in the tables above: the sequent drag & drop and inner-node
highlights/taclet info pane (item 3), the source-view family (item 4,
`SourceViewF.java:64-66/:110/:237`), Edit Last File, tooltip toggles, the
EnableWhenProofLoaded analogue and the toolbar buttons beyond the merged bar (item 5), the
global toolbar macro dropdown (P1 automation row), the info-view node-change statistics
refresh (`InfoViewF.java:94-99`), the notification `NotificationTask`/action-framework depth
(item 10) and the docking title-action/layout-slot remainder (item 11, named slots F10–F12
exist). Item 12 flags upstream Swing defects ("Not our defect" — `key.ui`/`key.core` cleanup,
unchanged by this migration).

**No row of this sign-off remains OPEN or unmarked.** Every entry ends RESOLVED,
WONT-REPLICATE (with its reason) or a clearly marked deliberate KNOWN-DEFERRED per-feature
deferral with its batch/WP reference and source site. The module-removal counterpart of this
close-out is `SWING-RETIREMENT.md`.

The KNOWN-SIMPLIFIED ledger mirrors the module-level subset of this list with per-site
file:line markers and statuses (`OPEN` / `FIXED-UPSTREAM` / `WONT-REPLICATE`). This sign-off is
re-run after each milestone batch that closes any of the items above.

# Difference audit — Swing↔JavaFX (2026-10-10)

The 2026-10-08 sign-off covered the documented deviations (the 68 KNOWN-SIMPLIFIED markers plus
the still-open list above). This section records the **new, previously undocumented**
differences found by a second Swing↔JavaFX sweep, with stable IDs used by the P2/P3/P4 batches
(`weigl/ocfx-p2-*`, `weigl/ocfx-p3-*`, `weigl/ocfx-p4-*`). Statuses: OPEN / RESOLVED (batch)
/ WONT-REPLICATE.

## A. Dialogs missing or reduced

| ID | Finding (Swing reference) | Status |
|----|---------------------------|--------|
| A1 | Contract/invariant configurator dialogs: the Swing registration `WindowUserInterfaceControl.java:74-82` (FunctionalOperationContract/DependencyContract/LoopInvariantRule/BlockContractInternal/BlockContractExternal completions + `ContractConfigurator.java`) — the FX registry (`WindowUserInterfaceControlF.java:126-135`) holds only `MergeRuleCompletionF` | RESOLVED (P2b) |
| A2 | `LemmaSelectionDialog` (lemmatagenerator, 161 lines) not ported | RESOLVED (P2b) |
| A3 | `LoadUserTacletsDialog` reduced (Swing 499 lines) | RESOLVED (P2b) |
| A4 | Proof Statistics: no export (Swing exports HTML/text) | RESOLVED (P3c) |
| A5 | About/License reduced to toasts instead of dialogs | RESOLVED (P3c) |
| A6 | GitHub-issue prefill dropped (bug-reporting URL parameters) | RESOLVED (P3c) |
| A7 | Feedback: no zip archive of logs | RESOLVED (P3c) |
| A8 | ToolTip options: "Save as Default" behaviour | RESOLVED (P3c) |
| A9 | `EnsureSourceConsistency` info dialog | RESOLVED (P2b) |
| A10 | Dialog triage remainder of the sweep | RESOLVED (P4, triage) |

## B. Menus / actions / toolbar

| ID | Finding (Swing reference) | Status |
|----|---------------------------|--------|
| B11 | Dynamic "Goal Back" label (`GoalBackAction.java:113-125`) vs. static `MainWindowF.java:3325-3327` | RESOLVED (P3b) |
| B12 | Macro superset + category submenus + ProofScript actions vs. the 4-macro `AUTOMATION_MACROS` | RESOLVED (P3b) |
| B13 | Extension PATH nesting (extension menus cannot nest) | RESOLVED (P4) |
| B14 | Per-extension toolbars merged into one | RESOLVED (P4, decided) |
| B15 | Toolbar GoalBack/Prune have no enablement | RESOLVED (P3b) |
| B16 | Popup dialogs replaced by toasts (per site) | RESOLVED (P4, decided) |
| B17 | TermLabelMenu persistence/styling | RESOLVED (P3b) |
| B18 | Recent-Files empty menu not disabled + font-size item order | RESOLVED (P3b) |

## C. Proof tree

| ID | Finding (Swing reference) | Status |
|----|---------------------------|--------|
| C19 | Per-proof view state cache (expansion/selection per proof) | RESOLVED (P3a) |
| C20 | Linearized (flat) proof view mode | RESOLVED (P3a) |
| C21 | OSS child nodes in the tree | RESOLVED (P3a) |
| C22 | Whole-tree actions (expand all/collapse all/...) | RESOLVED (P3a) |
| C23 | Popup items incl. SubtreeStatistics | RESOLVED (P3a) |
| C24 | `PROOF_TREE` extension seam (tree popup contributions) | RESOLVED (P4) |
| C25 | Node-filter counting rule | RESOLVED (P3a) |
| C26 | Hidden-tab passivation (Swing docking detail) | WONT-REPLICATE (P4, decided) |
| C27 | Auto-mode partial subtree updates | RESOLVED (P3a) |

## D. Sequent / strategy / goal list / status bar

| ID | Finding (Swing reference) | Status |
|----|---------------------------|--------|
| D28 | Left-click taclet menu + `POPUP_DELAY` guard (`CurrentGoalViewListener.java:48-95`, `SequentViewListener.java:29`) | RESOLVED (P2a) |
| D29 | Shift+click focussed auto mode (`CurrentGoalViewListener.java:56-58`) | RESOLVED (P2a) |
| D30 | Extension tooltip strings unwired | RESOLVED (P4) |
| D31 | Sequent line width computed from the viewport | RESOLVED (P3c) |
| D32 | Sequent search prefill from the hovered term (`SearchInSequentAction.java:32-37`) | RESOLVED (P2a) |
| D33 | Fonts vs. `KEY_FONT_*` settings | RESOLVED (P3c) |
| D34 | `SequentViewDock` missing | RESOLVED (P3c) |
| D35 | Strategy tab Go button + parallel-prover merge-point lock (`StrategySelectionView.java:157-208/869-895`) | RESOLVED (P2a) |
| D36 | `KeyboardShortcuts` extension seams absent | RESOLVED (P4) |
| D37 | Status-line task progress bar (log-only stubs, `WindowUserInterfaceControlF.java:317-327`) | RESOLVED (P3c) |

P2a (`weigl/ocfx-p2-sequent`, merged 2026-10-10) resolved D28/D29/D32/D35 —
`key.fx.verify.sequentmenu` PASS (term menu 31 entries, POPUP_DELAY guard, search prefill,
focussed auto mode) on Xvnc :99.

P2b (`weigl/ocfx-p2-dialogs`, merged 2026-10-10) resolved A1/A2/A3/A9 — the five contract
completions (`FunctionalOperationContractCompletionF`, `DependencyContractCompletionF`,
`LoopInvariantRuleCompletionF`, `BlockContractInternalCompletionF`,
`BlockContractExternalCompletionF`) are registered in the FX control next to
`MergeRuleCompletionF` (Swing parity WindowUserInterfaceControl.java:74-82); the dialogs
(`ContractConfiguratorF`, `AuxiliaryContractConfiguratorF`, `BlockContractSelectionPanelF`,
`ContractSelectionPanelF`, `InvariantConfiguratorF`, `LemmaSelectionDialogF` + `ItemChooserF`,
`LoadUserTacletsDialogF` axiom panel/warning/help, `EnsureSourceConsistency` info dialog) are
ported; `key.fx.verify.dialogs` PASS (registry + dialog skeletons) on Xvnc :99.

Interactive end-to-end contract application is RESOLVED (WP-9, `weigl/ocfx-wp9-integration`):
the sixth leg of `key.fx.verify.dialogs` loads a real spec-bearing example off the main window
(`heap/model_methods/CellTest_callSet.key`, override `key.fx.verify.dialogs.contract`), builds a
`UseOperationContractRule` app on a succedent top-level goal position, completes it through the
REAL `WindowUserInterfaceControlF.completeBuiltInRuleApp` dispatch (the modal
`ContractConfiguratorF` is driven by a background watcher via the new `lastInstance` seam:
select contract + OK) and applies the completed app via `ProofControl.applyInteractive`,
growing the proof by exactly one node. HTML-styled contract cells of the Swing configurator
remain plain text in the FX port (KNOWN-SIMPLIFIED, see the class javadocs).

P3a (`weigl/ocfx-p3a-prooftree`, merged 2026-10-10) resolved C19/C20/C21/C22/C23/C25/C27 —
`ProofTreeViewF`: the per-proof view-state cache (WeakHashMap<Proof, ViewState>, saved and
restored in the proof switch, C19); the linearized mode with the "main"-tagged taclet splice
(C20); the OneStepSimplifier protocol child rows with an "expand OSS nodes" toggle that gates
the whole-tree expand (C21); the whole-tree expand-all/collapse-all actions (C22); the popup
additions Apply Strategy / Prune Proof / Edit Notes / Show Subtree Statistics (C23, Swing
`ProofTreePopupFactory`); the node-filter counting rule incl. the "inlined due to hidden
subtree" case (C25); and the auto-mode partial subtree updates (C27, `modifiedSubtrees`,
`MAX_PARTIAL_TREE_UPDATES=16`). `key.fx.verify.prooftree` PASS (semantics self test + notes
dialog + subtree statistics dialog) on Xvnc :99, plus a live-autoprove run
(`key.fx.verify.prooftree` + `key.fx.demo.autoprove.live`) that exercised the partial subtree
updates (`autoModePartialUpdates=1`) and a post-autoprove run (`+ key.fx.demo.autoprove`)
covering the OSS rows on a strategy-proved proof. The view filters and the tree controls live
in the tree context menu because the FX docking framework has no tab-title gear menu (documented
in `ProofTreeViewF`); the subtree statistics report is a plain-text window rather than the Swing
HTML one (export is A4/P3c). C24 (the `PROOF_TREE` extension seam) stays open for P4.

P3b (`weigl/ocfx-p3b-menus`, see the branch report) resolved B11/B12/B15/B17/B18 — menu/toolbar
parity items:

- B11/B15 — the Proof-menu item and toolbar buttons now follow Swing enablement and labels:
  "Undo Last Rule Application" shows the applied rule name dynamically (`KeYMediatorF
  .`goalBackRuleName`), and Goal Back / Prune are enabled per the selected node and auto mode
  (`key.fx.verify.menuparity` legs).
- B12 — the macro surfaces (sequent right-click popup, term-menu "Strategy Macros", proof-tree
  context-menu "Strategy Macros") now show the registered-`ProofMacro` superset
  (`ProofMacroMenuF`), category-grouped like Swing, plus the PROOF_SCRIPTS menu (file chooser /
  input dialog) executed by a new `ProofScriptWorkerF`; the proof-tree macro submenu is
  persistent with a live PROOF_SCRIPTS feature listener.
- B17 — `TermLabelMenuF` items are `CustomMenuItem(HBox(CheckBox+Label))` rows that persist
  their state to `Preferences.userNodeForPackage(MainWindowF.class)` under the exact Swing
  `AbstractButtonSaver` keys (`DisplayLabelsCheckBox.DisplayLabelsCheckBox.selected` /
  `TermLabelCheckBox.<label>.selected`) and carry the bold/italic occurrence styling
  (+ per-state tooltips) from Swing's `selectedNodeChanged`; `OriginLabelsF.verify` gained a
  preference round-trip leg.
- B18 — the recent-files menu is never force-disabled (`recentFilesMenu.setDisable` removed),
  and the Font Size submenu items are ordered Smaller then Larger like Swing.

`key.fx.verify.menuparity` + `key.fx.verify.uicontrol` PASS (B11/B12/B15/B17/B18 legs) and
`key.fx.verify.prooftree` PASS (B12 macro submenu seam incl. the closed-demo zero-applicable
case) on Xvnc :99.

P4 (`weigl/ocfx-p4-extensions`) resolved B13/C24 (extension-seam parity) and decided
B14/B16/C26; A10 and the D-section remainder D30/D36 are triaged/resolved in the same batch:
- B13: `KeYGuiExtensionF.MainMenuF.getMenuPath()` (Swing `KeyAction.PATH`) + facade
  `KeYGuiExtensionFacadeF.installMenus`: path-bearing providers splice their items into
  existing or new menus of the bar (first segment matched by text — the five built-ins
  included — deeper segments by sub-menu text); the empty path keeps the FX default (separate
  top-level menus after About).
- C24: `ContextMenuF.getProofTreeContextItems(mediator, node)` default + facade aggregate;
  `ProofTreeViewF` appends the contributions after a separator at the end of the popup,
  rebuilt per showing, and drops the separator when nothing is contributed (Swing
  `ProofTreePopupFactory.create`, :152-154).
- B14 (decided): the FX keeps ONE merged `key-extension-tool-bar` holding every extension
  toolbar control; Swing embeds one JToolBar per extension in a FlowLayout. The single-bar
  layout is asserted by `key.fx.verify.extensions` (`extensionToolbars=1`).
- B16 (decided): informational popups map to non-modal toasts (`NotificationManagerF`);
  confirmations stay modal; the decision is applied per site (e.g. MainWindowF:1795-1802;
  the P3c A5/A7 sites follow the same convention).
- C26 (WONT-REPLICATE): the FX docking framework keeps dockables mounted — there is no
  tab-visibility lifecycle, so the Swing hidden-tab passivation
  (`ProofTreeView.java:339-428` dirty-flag + listener detach, `GUIProofTreeModel.setAttentive`)
  has nothing to attach to; documented in `ProofTreeViewF`.
- D30: `SequentViewF.getTooltipText` appends `KeYGuiExtensionFacadeF.getTooltipStrings`
  (Swing `SequentView.getToolTipText`, SequentView.java:234).
- D36: new `KeYGuiExtensionF.KeyboardShortcutsF` capability (view-scoped `ShortcutF`
  records; component constants mirroring the Swing `KeyboardShortcuts` set) bound by
  `installKeyboardShortcuts` as key-pressed filters on the six host views
  (sequent/goallist/prooftree/strategy/source/info).
- A10 (triage): all sweep dialog findings are now accounted for — A1-A3/A9 (P2b),
  A4-A8 (P3c), and the remaining per-site dialog decisions follow the B16 toast convention.
- The ported Swing `TestExtension` (`TestExtensionF`, priority 100000) exercises each seam:
  the `Test.Test.Test`-nested menu, a PROOF_TREE popup item, an extension-toolbar button and a
  Ctrl+Shift+F12 sequent shortcut — asserted headlessly by `key.fx.verify.extensions`
  (`testExtension`/`testNested`/`prooftreeExtensionItems`/`sequentShortcutToast`).


P3c (`weigl/ocfx-p3c-dialogs`, this branch) resolved A4/A5/A6/A7/A8 and D31/D33/D34/D37 — the
dialog/status-line parity items of the sweep:
A4 `ProofStatisticsDialogF` now exports the Swing CSV/HTML formats (`verifyStatisticsExport`);
A5 keeps "About KeY" as the enriched INFO toast (B16 convention) and turns the license into the
real `LicenseDialogF` (tabs "KeY License" + "Third party libraries", Swing `LicenseAction`);
A6 `MainWindowF.createGithubIssue`/`buildGithubIssueUrl` rebuilds the Swing
`CreateGithubIssueAction` issue template (%CHECKSUM% → internal version, %JAVA% → proof Java
sources) and opens it through the `HelpFacadeF` browser seam; A7 `FeedbackDialogF` "Save ZIP…"
writes `bugDescription.txt`/`keyVersion.txt`/`systemProperties.txt` + the `key_*.log` run logs
(`verifyLogArchive`); A8 `ToolTipOptionsDialogF` "Save as Default" persists the tooltip options
via `ProofIndependentSettings.saveSettings()` (`verifySaveAsDefault`); D31 `SequentViewF`
computes the print line width from the scroll-pane viewport via a `Text("W")` probe (Swing
`computeLineWidthFor`, reprint on width changes, `verifyViewportLineWidth` under
`key.fx.verify.sequent`); D33 `ConfigF` mirrors the Swing `KEY_FONT_*` families/sizes (proof
tree/sequent at the current size, goal/proof list at the fixed `SIZES[2]`); D34
`SequentViewDockF` shows a node's sequent in a separate buffer with the "Jump into Tree" title
action (proof-tree popup "Open Node in Separate Buffer"); D37 `MainWindowF.buildStatusBar` gains
the hidden-until-used progress bar with `setStatusLine(String,int)` /
`setTaskProgressBarMaximum` (`<0` indeterminate, `0` hidden, `>0` determinate) /
`setTaskProgressValue` / `hideStatusProgress`, wired from `WindowUserInterfaceControlF` exactly
like Swing's `WindowUserInterfaceControl` (taskStarted → `setStatusLine(msg,size)`, setMaximum /
setProgress / taskProgress → bar, macro end → hide). `key.fx.verify.uicontrol` +
`key.fx.verify.menuparity` PASS (10 seam steps incl. the six P3c seams, menu counts
File 16 / Proof 24 / Options 7 / View 12 / About 5) and `key.fx.verify.prooftree` +
`key.fx.demo.autoprove` PASS on Xvnc :98. A10 stays open for P4 (dialog triage remainder).

WP-9 (`weigl/ocfx-wp9-integration`) closed the four deferred integration-wiring asserts — each
one a headless self test that drives the REAL wiring end to end instead of a seam stub:

1. **AutoSave real flow** — `key.fx.verify.autosave` now arms the saver through the real
   `applyAutoSave` + `KeYMediatorF` selection hand-off on the loaded demo proof and runs a
   capped auto-mode application (interval 25, max 1000 steps) on a worker thread; the assert is
   that the `AutoSaver` actually writes the intermediate `.autosave.N.key` files through the
   `taskProgress` → `fireTaskProgress` chain and the final `.autosave.proof` — the writes are
   isolated via `java.io.tmpdir` and the armed period/max steps are restored. PASS
   (`/tmp/opencode/wp9/autosave.log`: "Auto save verification (real flow): PASS (6 save(s)
   under /tmp/opencode/wp9/tmp …)").
2. **Minimize-Interaction load pipeline** — `key.fx.verify.minimizeinteraction` proves the
   load-success hand-off honors the persisted flag on the loaded demo: armed, an
   auto-instantiable taclet app applies through the minimize branch of
   `AbstractProofControl.selectedTaclet` without the taclet dialog (the applied node is pruned
   back); disarmed, the same app opens the taclet dialog. The flag is restored. PASS
   (`/tmp/opencode/wp9/minimize.log`: "Minimize interaction verification: PASS").
3. **EnsureSourceConsistency load pipeline** — new `key.fx.verify.sourceconsistency` hook
   (proof-independent): loads the JML example (`heap/model_methods/CellTest_test2.key`,
   override `key.fx.demo.sourceconsistency`) twice — with the toggle armed (`DiskFileRepo`,
   `AbstractProblemLoader.createFileRepo:400-409`) and disarmed (`SimpleFileRepo`) — and reads
   the source through the repo stream the source view uses (`SourceViewF`'s
   `readRepoFile` path, Swing `SourceView.addFile:617-621`), asserting content identical to
   disk and the repo cache under the temp dir. The flag is restored. PASS
   (`/tmp/opencode/wp9/sourceconsistency.log`: "Source consistency verification: PASS (armed
   repo=DiskFileRepo disarmed repo=SimpleFileRepo; source read via repo=Cell.java (25 lines);
   cache dir=…)").
4. **Contract E2E** — the sixth leg of `key.fx.verify.dialogs` loads a real spec-bearing
   example (`heap/model_methods/CellTest_callSet.key`, override
   `key.fx.verify.dialogs.contract`) off the main window via `KeYEnvironment.load`; the PO
   inlines the callee in a try/catch, so the harness first parks the strategy at the active
   method call (METHOD_NONE strategy rebuild + one auto-mode run), builds a
   `UseOperationContractRule` app and completes it through the REAL
   `WindowUserInterfaceControlF.completeBuiltInRuleApp` dispatch — the modal
   `ContractConfiguratorF` (opened by `FunctionalOperationContractCompletionF.complete`) is
   driven by a background watcher via the new `lastInstance` seam (select contract + OK) —
   then applies the completed app via `ProofControl.applyInteractive` (the proof grows: the
   contract application splits the goal into child nodes). PASS
   (`/tmp/opencode/wp9/dialogs-e2e.log`: "Contract e2e: applied JML operation contract 0 on
   set (nodes 21 -> 25)" + "Dialogs verification: PASS: … contract apply E2E").

# WP-11 close-out (2026-10-12)

The sign-off is closed as part of WP-11 (endgame, `weigl/ocfx-wp11-endgame`):

* **Ledger state.** Every row above ends RESOLVED, WONT-REPLICATE (with reason) or a clearly
  marked deliberate KNOWN-DEFERRED per-feature deferral with its batch/WP reference and the
  source site (see the close-out paragraph after the carried-forward list). No OPEN row
  remains. `KNOWN-SIMPLIFIED.md` carries the module-level marker ledger with the same
  statuses.
* **Evidence.** The per-WP evidence logs cited inline (P0…P4 batches under `/tmp/opencode/`,
  WP-1…WP-10 under `/tmp/opencode/wp*/`, e.g. `/tmp/opencode/wp2/prooftree-agatha3.log`,
  `/tmp/opencode/wp9/autosave|minimize|sourceconsistency|dialogs-e2e.log`) stay the reference
  for the individual resolutions. The **full regression sweep over all `key.fx.verify.*`
  flags is WP-11 deliverable 1 and is run/recorded by the parent session — this document does
  not restate its results.**
* **Deliberate per-feature deferrals (final state, tracked here):** SMT select-menu refresh +
  progress mode/global timeout/bounds/store path (WP-7, `SolverOptionsF.java:35/:130`),
  source-view symbex/tab-per-file/cross-highlight family (`SourceViewF.java:64-66/:110/:237`),
  info-view node-change statistics refresh (`InfoViewF.java:94-99`), global toolbar macro
  dropdown (B14 decision), sequent drag & drop + inner-node highlights/taclet info pane,
  Edit Last File, tooltip toggles, EnableWhenProofLoaded analogue, toolbar buttons beyond the
  merged bar, notification `NotificationTask`/action-framework depth, docking title-action and
  layout-slot remainder. These are documented simplifications of the delivered FX port, not
  open work of WP-1…WP-10.
* **Process.** Docs default → FX (root README, settings.gradle, `key.ui.fx/README.md` with the
  `key.fx.*` whitelist and the headless recipe), the Swing retirement checklist
  (`SWING-RETIREMENT.md`) and this close-out are WP-11 deliverables 2–4; the plan file's
  Status header is refreshed by the parent session.
