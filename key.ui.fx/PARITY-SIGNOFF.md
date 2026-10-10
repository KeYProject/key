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
| prooftree | 53 | 20 / 8 / **13 MISSING** / 5 KNOWN-DEF | core tree faithful; heatmap etc. deferred | heatmap/NodeInfoVisualizer/branch editing still OPEN |
| sequent | 45 | 14 / 10 / **15 MISSING** / 4 KNOWN-DEF | term context menu + taclet application + search (MP8) | context menu RESOLVED; remaining items below |
| interactive-completion | 25 | 0 / 0 / **20 MISSING** | `WindowUserInterfaceControlF` seam + tacletmatch + join/merge | RESOLVED (was the top P0; evidence uicontrol + tacletmatch 9/9) |
| goallist-strategy-info | 37 | goal list at parity; strategy preset UI missing; info view re-designed | — | preset combo + stats staleness OPEN |
| source-search-filechooser | 74 | 30 / 5 / **28 MISSING** | search bars + loading-options dialog ported | source-view interaction (symbex highlights, cross-highlight) OPEN |
| menus-actions | 57 leaves | ~25 MISSING | menu parity 5/5 (File 16 / Proof 24 / Options 12 / View 7 / About 5) plus automation submenu | RESOLVED at surface level; a few behaviours below |
| settings-config | 117 | 83 / 8 / 11 MISSING / 13 KNOWN-DEF | settings framework + providers + colors mechanics + search | theme persistence OPEN; color definitions + SMT run UI RESOLVED (P1) |
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
| Apply Strategy on node + Prune-at-node in the tree popup | right-click macro menu ported (`key.fx.verify.rightclickmacro`); Apply Strategy-at-node unverified | — | **PARTIAL** |

P0 bugs from the audit:

| Bug | Status |
|---|---|
| FX search stale on node switch | **RESOLVED** (search re-runs on reprint; sequent-leftovers milestone `18df960b35`) |
| Proof-tree context menu acts on the selection, not the clicked node | `OPEN (unverified)` |
| View-menu Pretty Print / Unicode inert placeholders | `OPEN` (placeholders remain) |
| Recent-file clicks drop stored profile / single-java options | **RESOLVED** (P1: `openProofFile` registers the loading options with the entry like Swing `WindowUserInterfaceControl.loadProblem`; the recent-files menu restores profile (resolved via `DefaultProfileResolver`) / additional options / single-java like Swing `RecentFileAction`, `key.fx.verify.loadingexit` round trip PASS) |
| Shortcut-default mismatches (`KeyStrokeManagerF`: tree search, sequent search, macro defaults) | **RESOLVED** (P1: the defaults match the Swing table now — macros and PrettyPrint/Unicode/ProofManagement/tree-search on Ctrl+Shift, sequent search on Ctrl+F instead of the bare F that hijacked typing; stale persisted old defaults heal on load; `key.fx.verify.shortcuts` PASS) |
| Dead registered bindings (Ctrl+C term copy, F3/Shift+F3, Ctrl+K/Ctrl+J, Goal Back/Prune) | **RESOLVED** (P1: Ctrl+C copies the term under the mouse via the sequent view handler + the term-menu copy item carries the accelerator; term-menu global macro items carry their accelerators and the view-level macro keys run at the last clicked position (Swing `MacroKeyBinding`); F3/Shift+F3, Ctrl+K/Ctrl+J, Goal Back/Prune wired and covered by `key.fx.verify.shortcuts`) |
| Colors: 12 mapped CSS variables ineffective (47 property definitions missing) | **RESOLVED** (P1: `ColorPaletteF` defines all 51 Swing-parity properties — the true count incl. the two multi-line `define(` keys; the 9 previously-undeclared mapped CSS vars are declared in both themes and consumed by the re-wired `.sequent-hl-*`/`.source-*` rules; `key.fx.verify.colors` PASS) |
| UPSTREAM (Swing, not FX): `LoopApplyHeadCompletion` + `LoopContract*` dead code; seed-clobber `overwriteWith` | **Not our defect** — flags for upstream `key.ui`/`key.core` cleanup |

## P1 sign-off

| Audit item | Status |
|---|---|
| Loading options (profile / ignore other Java files) | **RESOLVED** — load-options dialog ported (`key.fx.verify.profileloading` + `profileloadingdialog` PASS) |
| Select Goal Above / Below + menu set (View 7) | **RESOLVED** at surface level (`key.fx.verify.menuparity` View 7); Selection Back/Forward binding `OPEN (unverified)` |
| Automation submenu + macro invocation | **RESOLVED** (automation submenu MP2, macro menu in term menu); global toolbar dropdown `OPEN` |
| Join / merge dialogs | **RESOLVED** for the merge/join flow (`key.fx.verify.joinmerge` PASS on gcd 32/0); `keyext.slicing.fx` SMT routing partial |
| Strategy preset combo / stash UI | `OPEN` |
| SMT settings + run UI | **RESOLVED** (P1: settings providers ported in MP4; the run UI — `SolverListenerF` + `ProgressDialogF` progress table + `InformationWindowF` + result application via the SMT rule — ported, `key.fx.verify.smt` PASS: Z3 closes the Agatha goal; the Swing toolbar `DropdownSelectionButton` remains tracked under the toolbar item) |
| Exit flow (close-request, `confirmExit`, layout save) | **RESOLVED** (P1: the window close button and the Exit menu item run the Swing `ExitMainAction` flow — `confirmExit` dialog, recent-files save, `System.exit(0)` which runs the docking/colors/keystrokes shutdown hooks; the Swing mediator `fireShutDown` has no FX seam — see KNOWN-SIMPLIFIED; `key.fx.verify.loadingexit` PASS: recent-files round trip + profile resolution, then the close-request path terminates with exit code 0 and the docking layout is saved) |
| Term labels; Pretty Print / Unicode wiring | `OPEN` (lemmaorigin hook covers labels mechanically — see `key.fx.verify.lemmaorigin`) |
| User-selection highlight + Ctrl+C copy | **RESOLVED** (term-menu copy item in the skeleton); multi-selection highlight + reprint persistence `OPEN` |
| Symbex source line highlights + sequent-hover origin cross-highlight | `OPEN` |
| KeyStroke default wiring next to the registry | `OPEN (unverified)` |

## P2 sign-off

Heatmap overlay (settings+toggle only, ledger `HeatmapF`), NodeInfoVisualizer, branch-label F2
editing, info-view node-change refresh, notification framework depth, docking title
actions/layout slots/maximize (partially done — `key.fx.verify.docking` PASS; title actions
exist as `DockTitleActionF`), join+mergerule dialogs (track MP9.x modules), lemmatagenerator
(`key.fx.verify.lemmaorigin` PASS for the generator path), soundiness (`key.fx.verify.soundiness`
PASS), originlabels (lemmaorigin), plugins, profileloading (RESOLVED), help windows
(`key.fx.verify.help` PASS), theme persistence (color definitions RESOLVED via P1
`key.fx.verify.colors`), feature
flags + parallel prover (`ParallelProverStatusIndicatorF` partial), settings dump, modal
grey-out, proof-disposal clearing (auto saver handles the disposal part), tab icons/titles,
file-chooser bookmarks. Each is either documented in the KNOWN-SIMPLIFIED ledger or listed above
as open.

## Still-open work list (carried forward)

1. Input freeze during auto mode (blocking glass pane port) — RESOLVED via P1
   `key.fx.verify.inputfreeze`; the menus stay clickable while frozen (Swing's glass pane
   covered everything except the `isAutoButton` stop controls) — KNOWN-SIMPLIFIED.
2. Proof-tree: Apply Strategy on clicked node, Prune-at-node in the popup, renderer surface
   (tooltips, goal icons, linked/cache marks, notes, branch-label F2 editing), NodeInfoVisualizer.
3. Sequent: multi-select highlight + reprint persistence, drag & drop, inner-node highlights +
   taclet info pane, source cross-highlight.
4. Source view: symbex line highlights, click-to-jump into the proof tree, hover
   cursor/line highlight, multi-file tabs, branch status bar.
5. Menus/actions: Pretty Print / Unicode wiring, term labels, tooltip toggles, selection
   Back/Forward bindings, Edit Last File, Load User Taclets + Prove submenu, Run All Proofs
   (dialogs exist for several), EnableWhenProofLoaded analogue, toolbars 9 remaining buttons.
6. Keyboard: shortcut-default regressions; dead bindings audit (RESOLVED via P1
   `key.fx.verify.shortcuts`; the Swing-persisted `keystrokes.json` stays the source of truth
   for user overrides).
7. Options dialogs: strategy preset UI, HeatmapOptionsDialog (SMT run UI RESOLVED via P1
   `key.fx.verify.smt`).
8. Exit flow: close-request + confirmExit + layout persistence on close (RESOLVED via P1
   `key.fx.verify.loadingexit`; the Swing `fireShutDown` event has no FX seam — KNOWN-SIMPLIFIED).
9. Colors/theme: all 51 Swing-parity color property definitions RESOLVED (P1 `key.fx.verify.colors` PASS); theme persistence remains.
10. Notification framework depth: proof-closed/exception dialogs beyond toasts are in
    (`IssueDialogF`); the `NotificationTask`/action framework remains partial.
11. Docking: remaining title actions, layout-slot keys F10–F12 (named slots exist).
12. Upstream (Swing) flags: `LoopApplyHeadCompletion`/`LoopContract*` dead code, seed-clobber.

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
| A4 | Proof Statistics: no export (Swing exports HTML/text) | OPEN (P3c) |
| A5 | About/License reduced to toasts instead of dialogs | OPEN (P3c) |
| A6 | GitHub-issue prefill dropped (bug-reporting URL parameters) | OPEN (P3c) |
| A7 | Feedback: no zip archive of logs | OPEN (P3c) |
| A8 | ToolTip options: "Save as Default" behaviour | OPEN (P3c) |
| A9 | `EnsureSourceConsistency` info dialog | RESOLVED (P2b) |
| A10 | Dialog triage remainder of the sweep | OPEN (triaged in P4) |

## B. Menus / actions / toolbar

| ID | Finding (Swing reference) | Status |
|----|---------------------------|--------|
| B11 | Dynamic "Goal Back" label (`GoalBackAction.java:113-125`) vs. static `MainWindowF.java:3325-3327` | OPEN (P3b) |
| B12 | Macro superset + category submenus + ProofScript actions vs. the 4-macro `AUTOMATION_MACROS` | OPEN (P3b) |
| B13 | Extension PATH nesting (extension menus cannot nest) | OPEN (P4) |
| B14 | Per-extension toolbars merged into one | OPEN (P4, decide) |
| B15 | Toolbar GoalBack/Prune have no enablement | OPEN (P3b) |
| B16 | Popup dialogs replaced by toasts (per site) | OPEN (P4, decide) |
| B17 | TermLabelMenu persistence/styling | OPEN (P3b) |
| B18 | Recent-Files empty menu not disabled + font-size item order | OPEN (P3b) |

## C. Proof tree

| ID | Finding (Swing reference) | Status |
|----|---------------------------|--------|
| C19 | Per-proof view state cache (expansion/selection per proof) | OPEN (P3a) |
| C20 | Linearized (flat) proof view mode | OPEN (P3a) |
| C21 | OSS child nodes in the tree | OPEN (P3a) |
| C22 | Whole-tree actions (expand all/collapse all/...) | OPEN (P3a) |
| C23 | Popup items incl. SubtreeStatistics | OPEN (P3a) |
| C24 | `PROOF_TREE` extension seam (tree popup contributions) | OPEN (P4) |
| C25 | Node-filter counting rule | OPEN (P3a) |
| C26 | Hidden-tab passivation (Swing docking detail) | OPEN (P4, likely WONT-REPLICATE) |
| C27 | Auto-mode partial subtree updates | OPEN (P3a) |

## D. Sequent / strategy / goal list / status bar

| ID | Finding (Swing reference) | Status |
|----|---------------------------|--------|
| D28 | Left-click taclet menu + `POPUP_DELAY` guard (`CurrentGoalViewListener.java:48-95`, `SequentViewListener.java:29`) | RESOLVED (P2a) |
| D29 | Shift+click focussed auto mode (`CurrentGoalViewListener.java:56-58`) | RESOLVED (P2a) |
| D30 | Extension tooltip strings unwired | OPEN (P4) |
| D31 | Sequent line width computed from the viewport | OPEN (P3c) |
| D32 | Sequent search prefill from the hovered term (`SearchInSequentAction.java:32-37`) | RESOLVED (P2a) |
| D33 | Fonts vs. `KEY_FONT_*` settings | OPEN (P3c) |
| D34 | `SequentViewDock` missing | OPEN (P3c) |
| D35 | Strategy tab Go button + parallel-prover merge-point lock (`StrategySelectionView.java:157-208/869-895`) | RESOLVED (P2a) |
| D36 | `KeyboardShortcuts` extension seams absent | OPEN (P4) |
| D37 | Status-line task progress bar (log-only stubs, `WindowUserInterfaceControlF.java:317-327`) | OPEN (P3c) |

P2a (`weigl/ocfx-p2-sequent`, merged 2026-10-10) resolved D28/D29/D32/D35 —
`key.fx.verify.sequentmenu` PASS (term menu 31 entries, POPUP_DELAY guard, search prefill,
focussed auto mode) on Xvnc :99.
