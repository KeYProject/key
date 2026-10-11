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
| `SolverListenerF.java:81` | results applied via `SMTProofApplyUserAction` (undoable history entry) with the `stopInterface` input freeze around it | direct `SMTRule` application on the FX thread (no undo entry for the automatic CLOSE-mode application; the apply runs synchronously on the FX thread, so a freeze around it would be unobservable — the auto mode freeze covers the long-running case) | OPEN |
| `InformationWindowF.java:24` | counterexample model tree (`CETree`) with line numbers (`TextLineNumber`) and the counterexample help tab | tabs per information entry as read-only monospaced text areas; model tree + line numbers + help tab not ported | OPEN |
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
| `ExplorationExtensionF.java:54` | registers `ExplorationModeModel` in the mediator registry and an `ExplorationRenderer` (purple border) into the proof tree | the registry seam now exists (WP-1: `KeYMediatorF.register(T, Class)`/`lookup(Class)`, Swing KeYMediator.java:589-626 parity); `ProofTreeViewF` still has no renderer-styling hook — the model is held directly by the provider; migrating the registration is WP-5's scope | OPEN (seam WP-1) |
| `ExplorationExtensionF.java:76` | — (extension description) | proof-tree styling and the hidden second-branch filter are deferred (no FX seam) | OPEN |
| `ExplorationExtensionF.java:280` | `mediator.register(model, ExplorationModeModel.class)` | provider holds the singleton model directly; the WP-1 register/lookup seam now exists on `KeYMediatorF`, migrating the registration is WP-5's scope | OPEN (seam WP-1) |
| `ExplorationExtensionF.java:363` | "Hide justification" routes through the proof-tree filter `HIDE_INTERACTIVE_GOALS` | persists the same `ViewSettings#setHideInteractiveGoals` flag and records the exploration-app state; the tree filter itself is deferred | OPEN |
| `ExplorationSequentMenuF.java:48` | `promptForTerm` modal retry-loop until the term is well-typed | single-shot `TextInputDialog`; malformed input or a sort mismatch aborts the action | OPEN |
| `ExplorationSequentMenuF.java:173` | sort-mismatch dialog, then re-opens the input dialog | single-shot; error alert and abort | OPEN |
| `ExplorationSequentMenuF.java:182` | malformed input re-prompts | single-shot abort | OPEN |
| `ExplorationStepsPanelF.java:56` | `Icons` (AWT/Swing) tab help button; icon images | help button not ported; status indicator uses ikonli FontAwesome solid/regular compass; pruning via `MainWindowF.getUserInterfaceControl().getProofControl()` | — |
| `ExplorationStepsPanelF.java:326` | prunes via `mediator.getUI().getProofControl()` | FX counterpart via the window's user-interface control; headless runs no-op | — |

## `keyext.isabelletranslation.fx` (4)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `IsabelleTranslationExtensionF.java:37` | `IsabelleTranslationAction.solveGoals` hands the generated theory to the external Isabelle solver (`IsabelleLauncher`) with a progress/model dialog | theories handed to the `IsabelleLauncher` on a background thread with the JavaFX progress dialog port (`IsabelleSolverProgressDialogF` + `IsabelleLauncherProgressDialogMediatorF`); launch failures show a "Launch failed!" alert and keep the theories accessible in the translation dialog | RESOLVED (WP-8): solver launch + JavaFX progress dialog port added; verify = `key.fx.verify.isabelle` DRY-RUN (fake solvers, no real Isabelle installation, scala-isabelle backend stays unloaded) |
| `IsabelleTranslationExtensionF.java:48` | — (extension description) | extension description now states the solver launch + progress dialog | RESOLVED (WP-8): restated row, see `IsabelleTranslationExtensionF.java:37` |
| `IsabelleTranslationRunnerF.java:28` | solver run + progress/model dialog | the runner translates on the background thread and then calls `IsabelleLauncher.launch(problems, timeout, 1)` like Swing; `IsabelleLauncher` is plain Java (only `IsabelleResourceController`/`IsabelleSledgehammerSolver` bodies touch `de.unruh.isabelle`, loaded lazily at launch execution) | RESOLVED (WP-8): solver run + progress/model dialog ported; sub-simplification: Apply closes solved goals directly without the undoable Swing `UserAction` wrapper (the FX mediator API has no user-action seam) |
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
| `TestgenExtensionF.java:59` | implements `Toolbar` and `Startup` in addition to the menu | `ToolbarF`/`StartupF` not implemented: the two toolbar actions become the two plain buttons of the status-line slot (no `ToolbarF` layout needed for two buttons; plain `Button`s stay constructible headless); the window is captured lazily through the settings panel instead of a `StartupF` hook; the menu slot is implemented in full | OPEN |
| `TestgenExtensionF.java:72` | window arrives via `Startup`/toolbar | `StatusLineF` does not receive the window and no `StartupF` hook exists, so the port captures it through the settings panel (the one SPI surface passing it) and wires enablement listeners on first capture; until then the buttons validate on click | OPEN |
| `TestgenExtensionF.java:133` | — (field doc) | the window field stays a plain `Object` (`MainWindowF` is not nameable in this module) and is `null` until the user opens the settings dialog | — |
| `TestgenExtensionF.java:155` | toolbar in the JToolBar | expressed through the status-line slot: a "Test Case Generation" `MenuButton` re-exposing the two menu items plus the two plain buttons | — |
| `TestgenExtensionF.java:193` | `SHORTCUT+T` bound via `KeyStrokeSettings` on the TestGen strategy macro (term context menu) | the accelerator lives on the main-menu item (double-fire with the status `MenuButton` would occur otherwise; the FX API has no macro-keybinding slot yet) | OPEN |
| `TestgenExtensionF.java:344` | enabled-state updates via the Swing action infrastructure | without a captured window the controls stay enabled and the run dialogs validate on click | OPEN |
| `TestgenSettingsProviderF.java:40` | settings provider with a named `MainWindowF` | `SettingsProviderF.getPanel/apply` declare `MainWindowF`, and naming it forces javac to complete `KeYEnvironment`'s class file, which fails on this module's classpath — the provider is a `java.lang.reflect.Proxy` that forwards the window as plain `Object` | — |
| `TestgenSettingsProviderF.java:50` | panel subclasses the Swing `SettingsPanel` base (row/validator/chooser helpers, working-copy change listeners) | plain `GridPane` of label/input rows (host wraps it in a `ScrollPane`) | — |
| `TestgenReflectionF.java:160` | `TGWorker` wraps the run in the mediator's auto-mode machinery with an immediate `StopRequest`/`SolverLauncher` stop | the facade route has no launcher handle — stopping interrupts the worker thread, which the generation macros honour between phases (the final Z3 CE launch runs until it returns) | OPEN |
| `TestgenReflectionF.java:220` | `SolverListener` opens a modal progress dialog and a results dialog showing the counterexample model | prints the SMT statistics (solved/invalid/unknown path conditions) and the found/not-found outcome into the run dialog's log; model inspection is left to the generated test data | OPEN |
| `TestGenerationTaskF.java:19` | worker puts the original proof into auto-mode machinery and stops cooperatively | `requestStop()` interrupts the worker thread (macros honour it between phases) | OPEN |
| `TestGenResultsDialogF.java:43` | dialog embeds a live `TestgenOptionsPanel` on its eastern edge | options stay exclusively in the Settings dialog (the global settings are re-read at run start); "Close" is disabled during the run like Swing; the generated-files list is a recursive listing of the output folder (Swing only logs "Writing test file") | OPEN |
| `TestGenResultsDialogF.java:154` | window available from the start | window may be `null` until the settings dialog was opened — the run is validated on click and starts with a hint otherwise | OPEN |
| `CounterExampleTaskF.java:21` | `SolverListener` modal progress + results dialogs with the counterexample model; auto-mode shell | prints statistics + outcome into the run log; auto-mode shell dropped | OPEN |
| `CounterExampleResultsDialogF.java:35` | counterexample model shown in modal result dialogs | only SMT statistics + found/not-found into the log; the dialog starts with a hint when the extension is not yet connected | OPEN |
| `CounterExampleResultsDialogF.java:131` | window available from the start | validated on click (frozen SPI passes the window only to the settings panel) | OPEN |
| `TestgenExtensionFTest.java:24` | — (test design) | unit tests are toolkit-free; control trees are asserted in-app only | — |
| `TestgenExtensionFTest.java:52` | — (test design) | documents that `ToolbarF`/`StartupF` are not implemented | — |

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
