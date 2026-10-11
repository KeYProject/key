# Consolidated ledger of KNOWN-SIMPLIFIED deviations

Every deliberate deviation of the JavaFX UI from its Swing original is marked at the source site
with a `KNOWN-SIMPLIFIED` comment or `<b>KNOWN-SIMPLIFIED:</b>` javadoc block. This file is the
single consolidated ledger: one row per marker, for `key.ui.fx` and all six keyext ports
(MP9.1–9.6). Row references are `Class.java:line` and point at the marker itself, which carries
the full sentence.

Marker counts per module:

| Module | Markers |
|---|---|
| `key.ui.fx` (contrib extensions + SMT run UI + exit flow + input freeze) | 7 |
| `keyext.caching.fx` | 10 |
| `keyext.exploration.fx` | 9 |
| `keyext.isabelletranslation.fx` | 4 |
| `keyext.slicing.fx` | 16 |
| `keyext.ui.testgen.fx` | 18 |
| `keyext.proofmanagement.fx` | 4 |
| **Total** | **68** |

To re-derive this table at any point: `grep -rn 'KNOWN-SIMPLIFIED' */src/main */src/test`.

The status column is for the close-out tracking: **OPEN** items are candidates for a later
milestone, **FIXED-UPSTREAM** items differ from a Swing bug that the port deliberately corrects,
**WONT-REPLICATE** items depend on Swing-only machinery with no FX counterpart.

---

## `key.ui.fx` — built-in contrib extensions (3)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `extension/contrib/HeatmapF.java:28` | `HeatmapExt` renders the heat highlight into the proof tree / sequent | menu + toolbar toggle + persisted `ViewSettings` options only; proof-tree heat overlay deferred | OPEN |
| `extension/contrib/HeatmapF.java:37` | — (doubles the `@Info` description) | same decision restated for the extension dialog | OPEN |
| `extension/contrib/ParallelProverStatusIndicatorF.java:27` | toggle button "SC" / "MT N×" with left-click toggle and right-click worker-count menu | plain `Label` showing the live auto-mode state ("Auto"/"Manual"), left-click toggles `PARALLEL_PROVER_ENABLED`, reacts to property changes; worker-count picker and button styling out of scope | OPEN |

## `key.ui.fx` — SMT run UI + exit flow + input freeze (4)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `SolverListenerF.java:81` | results applied via `SMTProofApplyUserAction` (undoable history entry) with the `stopInterface` input freeze around it | RESOLVED (WP-7): `SolverListenerF.applyResults` runs `SMTProofApplyUserActionF.actionPerformed()` — the `UserActionF` port (name "Close: %d goals by SMT", undo = prune to the original nodes + default selection, canUndo = all applied nodes still findable) executed inside the mediator auto-mode context with `stopInterface` freeze around it (Swing SolverListener.java:209-221 parity); the `UserActionListenerF` seam (`KeYMediatorF.addUserActionListener/fireActionPerformed`) is asserted by the undoable-apply extension of `key.fx.verify.smt` (freeze events, undo re-opens a goal) | RESOLVED (WP-7) |
| `InformationWindowF.java:24` | counterexample model tree (`CETree`) with line numbers (`TextLineNumber`) and the counterexample help tab | RESOLVED (WP-7): the counterexample tabs are ported — the `CETreeF` model tree (double-click expansion of `#o`/`#l`/`#s` reference leaves, `IGNORECASE_COMPARATOR` rows), the Help tab (`CE_HELP` text) and a simple line-number gutter for the information tabs (FX has no `TextLineNumber`); the window retitles to "Counterexample ..." for the Z3 CE solver with a model (Swing InformationWindow.initModel, :88-101); asserted by `key.fx.verify.testgen` | RESOLVED (WP-7) |
| `MainWindowF.java:3721` | exit fires the mediator shutdown event (`fireShutDown` → `GUIListener.shutDown`) | RESOLVED (WP-1): `KeYMediatorF` has the GUI-listener registry (`GUIListenerF`, `addGUIListener`/`removeGUIListener`, Swing `KeYMediator.java:306-410`) and the exit flow fires the event (`mediator.fireShutDown(new EventObject(this))`); the Swing listener's window-hiding is the `Platform.exit` of the flow | RESOLVED (WP-1) |
| `MainWindowF.java:2659` | the glass pane covered the whole content pane and re-delivered events only to components marked `isAutoButton` (automation/stop buttons + status-line abort button) | WONT-REPLICATE (WP-1 decision): the overlay keeps covering only the views area (workspace + drawers). The menu bar/toolbar proof actions are disabled during auto mode anyway (enablement binds to `mediator.autoModeRunningProperty()`), so blocking clicks on inert controls adds no protection; the automation macro items are enabled during auto mode by Swing parity so a click stops the run (MacroAutomationAction.java:48-61) and blocking them would regress that intent; the status bar must stay live for the progress display; and the stop controls the Swing glass pane kept live are the same controls the FX toolbar keeps live | WONT-REPLICATE (WP-1) |

## `keyext.caching.fx` (10)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `CachingExtensionF.java:95` | `CachingSettingsProvider.getCachingSettings()` on the keyext compile path | the FX module owns the `ProofCachingSettings` singleton via `CachingSettingsProviderF.getCachingSettings()` (Swing provider not loadable on the FX compile path) | FIXED-UPSTREAM |
| `CachingExtensionF.java:129` | menu checkbox instantiated eagerly | created lazily on first use (constructing controls needs the FX toolkit; the SPI may instantiate the provider headless) | — |
| `CachingExtensionF.java:735` | opens the interactive `ReferenceSearchDialog` (per-goal table + "Apply") | RESOLVED (WP-4): the dialog is ported as `ReferenceSearchDialogF` (per-goal `TableView` snapshot like Swing `ReferenceSearchTable`, "Close"/"Apply" button row, progress label/bar) and opened by the status-button click; the "Apply" action copies the referenced steps via `DefaultReferenceSearchDialogListenerF` (core `CopyReferenceResolver` inside the mediator auto-mode context + statistics window); asserted by `key.fx.verify.caching` | RESOLVED (WP-4) |
| `CachingExtensionF.java:778` | feeds `mediator.getCurrentlyOpenedProofs()` to the reference search | RESOLVED (WP-4): `openedProofs()` returns the live WP-1 seam list (`KeYMediatorF.getCurrentlyOpenedProofs()`, kept live by the `ProofManagerF` sync in `MainWindowF`); the extension's tracked proofs remain only the toolkit-free fallback | RESOLVED (WP-4) |
| `CachingPruneHandlerF.java:26` | iterates `mediator.getCurrentlyOpenedProofs()` | RESOLVED (WP-4): iterates `CachingExtensionF.openedProofs()` (the WP-1 seam list) like Swing `CachingPruneHandler.java:51` | RESOLVED (WP-4) |
| `CachingSettingsProviderF.java:37` | keyext registers the caching settings into `ProofIndependentSettings` | the FX module owns and registers the same singleton itself (shared persisted object with the Swing keyext via the registry) | — |
| `CachingSettingsProviderF.java:109` | writes `strategySearch.isEnabled()` (latent Swing bug — `JCheckBox#isEnabled` always true, persisted `true`) | writes the checkbox *selection* — the behaviour the panel visibly offers | FIXED-UPSTREAM |
| `CopyBeforeDisposeF.java:25` | wraps the copy into `mediator.initiateAutoMode(...)`/`finishAutoMode(...)` | RESOLVED (WP-4): the copy is wrapped into the WP-1 auto-mode context API (`initiateAutoMode(newProof, true, false)` around the copy, `finishAutoMode(newProof, true, true, () -> {})` in the finally, Swing CachingExtension.java:312-319 parity); the direct resolver call remains only the null-mediator (toolkit-free) fallback | RESOLVED (WP-4) |
| `CachingExtensionFTest.java:27` | — (test design) | unit tests are toolkit-free; control-level SPI contracts are verified by the in-app `key.fx.verify.extensions` hook | — |
| `CachingExtensionFTest.java:69` | — (test design) | asserts the FX-module-owned singleton identity and registry idempotence | — |

## `keyext.exploration.fx` (9)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `ExplorationExtensionF.java:54` | registers `ExplorationModeModel` in the mediator registry and an `ExplorationRenderer` (purple border) into the proof tree | RESOLVED (WP-5): the provider registers the model through the WP-1 seam (`mediator.register(model, ExplorationModeModel.class)`, consumers look it up; the provider-held singleton stays as the fallback for consumers without a mediator) and registers the `ExplorationRendererF` cell styler (the purple border/background + "Exploration Action Performed" tooltip title on nodes carrying `ExplorationNodeData`) through the new `ProofTreeViewF` renderer-styling hook (`CellStyler`/`Style`, Swing `Styler` parity) | RESOLVED (WP-5) |
| `ExplorationExtensionF.java:76` | — (extension description) | RESOLVED (WP-5): the restated decision is superseded — proof-tree styling is the `ProofTreeViewF.CellStyler` hook and the hidden second-branch filter routes through the (P3a-implemented) `HIDE_INTERACTIVE_GOALS` filter; the extension description states the parity | RESOLVED (WP-5) |
| `ExplorationExtensionF.java:280` | `mediator.register(model, ExplorationModeModel.class)` | RESOLVED (WP-5): the `init` hook registers the model through the WP-1 `KeYMediatorF.register/lookup` seam; the provider keeps holding the singleton as the lookup fallback (verified by `key.fx.verify.exploration` + the toolkit-free `initRegistersModelInMediatorRegistry` test) | RESOLVED (WP-5) |
| `ExplorationExtensionF.java:363` | "Hide justification" routes through the proof-tree filter `HIDE_INTERACTIVE_GOALS` | RESOLVED (WP-5): the toggle routes through `ProofTreeViewF.applyHideInteractiveGoals` — the same persisted `ViewSettings#setHideInteractiveGoals` flag the FX `HIDE_INTERACTIVE_GOALS` filter honours (P3a) plus the tree rebuild (Swing `ExplorationModeModel.setShowInteractiveBranches` → `GUIProofTreeModel.setFilter` parity) | RESOLVED (WP-5) |
| `ExplorationSequentMenuF.java:48` | `promptForTerm` modal retry-loop until the term is well-typed | RESOLVED (WP-5): faithful port of the Swing retry-loop (ExplorationAction.java:35-65) — the input dialog re-opens until a well-typed term of the required sort is entered; the dialog/error surface sits behind the `PromptHandler` seam for headless unit tests | RESOLVED (WP-5) |
| `ExplorationSequentMenuF.java:173` | sort-mismatch dialog, then re-opens the input dialog | RESOLVED (WP-5): the loop shows the "Sort mismatch" error and re-prompts (unit test `retryAfterSortMismatch`, in-app `key.fx.verify.exploration` accepts bad-then-good input) | RESOLVED (WP-5) |
| `ExplorationSequentMenuF.java:182` | malformed input re-prompts | RESOLVED (WP-5): the loop shows the "Malformed input" error and re-prompts (unit test `retryAcceptsBadThenGoodInput`) | RESOLVED (WP-5) |
| `ExplorationStepsPanelF.java:56` | `Icons` (AWT/Swing) tab help button; icon images | help button not ported; status indicator uses ikonli FontAwesome solid/regular compass; pruning via `MainWindowF.getUserInterfaceControl().getProofControl()` | — |
| `ExplorationStepsPanelF.java:326` | prunes via `mediator.getUI().getProofControl()` | FX counterpart via the window's user-interface control; headless runs no-op | — |

## `keyext.isabelletranslation.fx` (4)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `IsabelleTranslationExtensionF.java:37` | `IsabelleTranslationAction.solveGoals` hands the generated theory to the external Isabelle solver (`IsabelleLauncher`) with a progress/model dialog | theories handed to the `IsabelleLauncher` on a background thread with the JavaFX progress dialog port (`IsabelleSolverProgressDialogF` + `IsabelleLauncherProgressDialogMediatorF`); launch failures show a "Launch failed!" alert and keep the theories accessible in the translation dialog | RESOLVED (WP-8): solver launch + JavaFX progress dialog port added; verify = `key.fx.verify.isabelle` DRY-RUN (fake solvers, no real Isabelle installation, scala-isabelle backend stays unloaded) |
| `IsabelleTranslationExtensionF.java:48` | — (extension description) | extension description now states the solver launch + progress dialog | RESOLVED (WP-8): restated row, see `IsabelleTranslationExtensionF.java:37` |
| `IsabelleTranslationRunnerF.java:28` | solver run + progress/model dialog | the runner translates on the background thread and then calls `IsabelleLauncher.launch(problems, timeout, 1)` like Swing; `IsabelleLauncher` is plain Java (only `IsabelleResourceController`/`IsabelleSledgehammerSolver` bodies touch `de.unruh.isabelle`, loaded lazily at launch execution) | RESOLVED (WP-8): solver run + progress/model dialog ported; sub-simplification: Apply closes solved goals directly without the undoable Swing `UserAction` wrapper (at WP-8 time the FX mediator API had no user-action seam; WP-7 added the `UserActionF` seam afterwards — see `SolverListenerF.java:81`) |
| `IsabelleSettingsProviderF.java:191` | reads the keyext configuration constants | the constants (`isabellePathKey`/`translationPathKey`/`timeoutKey`) are package-protected in keyext; their stable string values are mirrored here | — |

## `keyext.slicing.fx` (16)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `SlicingExtensionF.java:49` | registers a proof-load listener through the Swing mediator | the registry now exists (WP-1: `KeYMediatorF.registerProofLoadListener`/`fireProofLoaded`, fired from `WindowUserInterfaceControlF.registerProofAggregate` like Swing WindowUserInterfaceControl.java:522); the `KeYSelectionListener` workaround still covers both "new proof loaded" and "selected proof switched" — migrating it is WP-6's scope | — |
| `SlicingExtensionF.java:249` | "Show dependency graph around this formula" renders the DOT excerpt through `PreviewDialog`/graphviz | shows the DOT source in a text dialog (the graphviz image renderer is Swing-only) | OPEN |
| `SlicingSettingsProviderF.java:29` | `SlicingSettings.setAggressiveDeduplicate` callable (same package) | setter is package-private in `org.key_project.slicing`; the toggle reflects the current setting but does not persist changes; the other two options persist normally | OPEN |
| `SlicingSettingsProviderF.java:144` | writes the aggressive-deduplicate flag | read-only (same package-private setter constraint; module may not modify keyext.slicing) | OPEN |
| `SlicingLeftPanelF.java:59` | panel summary: graphviz rendering, iterative fixed point, HTML statistics/timings | DOT-as-text, single slicing iteration, plain-text statistics, plain-label timings (details on the individual rows) | OPEN |
| `SlicingLeftPanelF.java:222` | "Slice proof to fixed point" opens the iterative `SliceToFixedPointDialog` | performs a single slicing iteration (identical to "Slice proof") | OPEN |
| `SlicingLeftPanelF.java:228` | — (tooltip for the fixed-point button) | restates the single-iteration decision | OPEN |
| `SlicingLeftPanelF.java:270` | file chooser with parent component | owner-less `FileChooser` (the drawer panel has no dedicated window) | — |
| `SlicingLeftPanelF.java:295` | rule statistics as HTML table with four sort buttons | plain-text rows with the default "total applications, descending" order | OPEN |
| `SlicingLeftPanelF.java:322` | renders the DOT to a PNG via the Swing graphviz executor and shows an image dialog | shows the DOT source text | OPEN |
| `SlicingLeftPanelF.java:377` | passes a headless `DefaultUserInterfaceControl` to the slicer | uses the FX window's own user-interface control (`ProblemLoaderControl`) so the loader callbacks stay FX-safe | — |
| `SlicingLeftPanelF.java:415` | loads the slice through the problem loader directly (keeps it out of the recent-files list) | takes the public load pipeline of the main window (`openProofFile`), which registers the file in the recent-files list | OPEN |
| `SlicingLeftPanelF.java:464` | execution timings as HTML table via `HtmlFactory` | one "Algorithm: time" line per measured activity | OPEN |
| `SlicingLeftPanelF.java:541` | panel grey-out via the Swing-only `SingleCoreFeatureGate` | checks the parallel-prover setting directly and disables the panel recursively | — |
| `SlicingLeftPanelF.java:618` | `HtmlDialog`/`PreviewDialog` | read-only multi-line text dialog stand-in | OPEN |
| `SlicingExtensionFTest.java:27` | — (test design) | unit tests are toolkit-free; the provider's JavaFX widget contributions are verified in-app | — |

## `keyext.ui.testgen.fx` (18)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `TestgenExtensionF.java:59` | implements `Toolbar` and `Startup` in addition to the menu | RESOLVED (WP-7): the extension implements `KeYGuiExtensionF.ToolbarF` + `StartupF` like Swing — the two actions are the plain `Button`s contributed through `getToolbarControls` and the window is captured at startup; the status-line `MenuButton` stand-in is dropped; asserted by the toolkit-free `capabilitySurface` test and `key.fx.verify.testgen` | RESOLVED (WP-7) |
| `TestgenExtensionF.java:72` | window arrives via `Startup`/toolbar | RESOLVED (WP-7): the `StartupF.init(window, mediator)` hook (plus the toolbar hook) hands the window to the extension at app startup, so the enablement listeners wire from the start; the settings panel remains the toolkit-free fallback capture | RESOLVED (WP-7) |
| `TestgenExtensionF.java:133` | — (field doc) | the window field stays a plain `Object` (`MainWindowF` is not nameable in this module); it is captured at startup through the `StartupF`/`ToolbarF` hooks (WP-7) | — |
| `TestgenExtensionF.java:155` | toolbar in the JToolBar | RESOLVED (WP-7): the two plain buttons of the Swing JToolBar, contributed through the `ToolbarF` hook; the status-line `MenuButton` stand-in is dropped | — |
| `TestgenExtensionF.java:193` | `SHORTCUT+T` bound via `KeyStrokeSettings` on the TestGen strategy macro (term context menu) | RESOLVED (WP-7): the `TestGenMacro` default (real FQN `de.uka.ilkd.key.testgen.macros.TestGenMacro`, Ctrl+Shift+T) is registered in the shared `KeyStrokeManagerF` (`defineDefault`) and drives the generate item's accelerator (`manager.binding(...).ifPresent(setAccelerator)` + `manager.register(item, id)`); asserted by `testGenMacroShortcutBinding` and `key.fx.verify.testgen` | RESOLVED (WP-7) |
| `TestgenExtensionF.java:344` | enabled-state updates via the Swing action infrastructure | RESOLVED (WP-7): with the startup capture the enablement listeners (selection, auto mode, SMT settings) wire from the start — the controls disable during runs (auto mode) and enable for a loaded proof with an installed z3 CE solver | RESOLVED (WP-7) |
| `TestgenSettingsProviderF.java:40` | settings provider with a named `MainWindowF` | `SettingsProviderF.getPanel/apply` declare `MainWindowF`, and naming it forces javac to complete `KeYEnvironment`'s class file, which fails on this module's classpath — the provider is a `java.lang.reflect.Proxy` that forwards the window as plain `Object` | — |
| `TestgenSettingsProviderF.java:50` | panel subclasses the Swing `SettingsPanel` base (row/validator/chooser helpers, working-copy change listeners) | plain `GridPane` of label/input rows (host wraps it in a `ScrollPane`) | — |
| `TestgenReflectionF.java:160` | `TGWorker` wraps the run in the mediator's auto-mode machinery with an immediate `StopRequest`/`SolverLauncher` stop | RESOLVED (WP-7): `generateTestcases` builds its own `SolverLauncher` and hands the handle to the caller via `launcherRef` (the Swing `stopSMTLauncher` parity, the facade hid its launcher) and every phase is guarded by a `shouldStop` flag (the cooperative `StopRequest` parity); the auto-mode shell lives in `TestGenerationTaskF` | RESOLVED (WP-7) |
| `TestgenReflectionF.java:220` | `SolverListener` opens a modal progress dialog and a results dialog showing the counterexample model | RESOLVED (WP-7): the CE search routes its `SolverLauncherListener` through the `SolverListenerFactoryF` hook answered by `CounterExampleTaskF` with a `SolverListenerF` — the modal progress dialog and the results/counterexample-model dialogs like Swing `SolverListener`; the reflective log-only listener is deleted | RESOLVED (WP-7) |
| `TestGenerationTaskF.java:19` | worker puts the original proof into auto-mode machinery and stops cooperatively | RESOLVED (WP-7): typed `Proof`/`KeYMediatorF` auto-mode shell (`initiateAutoMode` in `call`, `finishAutoMode` in the terminal-state hooks, the Swing `TGWorker.start/done` parity) and cooperative stop (`shouldStop` between the phases, `SolverLauncher` stop + worker-interrupt backup, the `interruptionPerformed` parity) | RESOLVED (WP-7) |
| `TestGenResultsDialogF.java:43` | dialog embeds a live `TestgenOptionsPanel` on its eastern edge | RESOLVED (WP-7): the dialog embeds the `TestgenOptionsPanelF` on its right edge (`root.setRight`, TGInfoDialog.java:126 parity) — KNOWN-SIMPLIFIED: the embedded panel writes into the global settings live (the Swing working copy was never applied from the run dialog, so its edits were lost — deliberate FX change); "Close" is disabled during the run like Swing; the generated-files list is a recursive listing of the output folder (Swing only logs "Writing test file") | RESOLVED (WP-7) |
| `TestGenResultsDialogF.java:154` | window available from the start | RESOLVED (WP-7): the window arrives at startup through the `StartupF` hook, so the run starts normally; the null-window hint remains the toolkit-free fallback path | RESOLVED (WP-7) |
| `CounterExampleTaskF.java:21` | `SolverListener` modal progress + results dialogs with the counterexample model; auto-mode shell | RESOLVED (WP-7): the auto-mode shell is restored (the Swing `CEWorker.start/done` parity: `initiateAutoMode` in `call`, `finishAutoMode` in the terminal hooks) and the listener route answers a `SolverListenerF` (the modal progress dialog + CE model dialogs) | RESOLVED (WP-7) |
| `CounterExampleResultsDialogF.java:35` | counterexample model shown in modal result dialogs | RESOLVED (WP-7): the counterexample model is shown in the `SolverListenerF` result dialogs (`InformationWindowF` with the `CETreeF` model tree); the run dialog keeps the pipeline log (side proof, semantics blasting) as documented | RESOLVED (WP-7) |
| `CounterExampleResultsDialogF.java:131` | window available from the start | RESOLVED (WP-7): the window is available from startup through the `StartupF` hook; the validated-on-click path remains the toolkit-free fallback | RESOLVED (WP-7) |
| `TestgenExtensionFTest.java:24` | — (test design) | unit tests are toolkit-free; control trees are asserted in-app only | — |
| `TestgenExtensionFTest.java:52` | — (test design) | asserts that `ToolbarF`/`StartupF` are implemented (WP-7) | — |

## `keyext.proofmanagement.fx` (4)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `CheckConfigDialogF.java:45` | `BlockingGlassPane` blocks input while the check runs (Stop-only pass-through) | explicitly disables the input controls while the check runs; "Run checkers" becomes "Stop" (the only enabled control); cancelling may leave partial output like the original | — |
| `CheckConfigDialogF.java:50` | bundle/report choosers via AWT `KeYFileChooser` with `.zproof`/`.html` filters | `FileChooser` with equivalent extension filters; file-only selection matches the Swing dialog | — |
| `CheckConfigDialogF.java:55` | opens the generated report via `Desktop.getDesktop().open` | opens it through the `HelpFacadeF` browser seam (`openExternal`, host services with a desktop fallback) — no AWT/Swing | — |
| `CheckConfigDialogF.java:212` | in-dialog browser/help | `HelpFacadeF` browser seam — see the class javadoc | — |

---

**What this ledger does not track:** ordinary porting work that is *faithful* to the Swing
original (the vast majority of the ~490 audited behaviors) and the deliberate feature additions
of the FX port (e.g. working search, editable dark theme column, extension status indicators).
Those are covered by `PARITY-SIGNOFF.md` and the per-module READMEs.
