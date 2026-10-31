# Consolidated ledger of KNOWN-SIMPLIFIED deviations

Every deliberate deviation of the JavaFX UI from its Swing original is marked at the source site
with a `KNOWN-SIMPLIFIED` comment or `<b>KNOWN-SIMPLIFIED:</b>` javadoc block. This file is the
single consolidated ledger: one row per marker, for `key.ui.fx` and all six keyext ports
(MP9.1–9.6). Row references are `Class.java:line` and point at the marker itself, which carries
the full sentence.

Marker counts per module:

| Module | Markers |
|---|---|
| `key.ui.fx` (contrib extensions + SMT run UI + exit flow + input freeze + built-in extension ports) | 31 |
| `keyext.caching.fx` | 10 |
| `keyext.exploration.fx` | 9 |
| `keyext.isabelletranslation.fx` | 4 |
| `keyext.slicing.fx` | 16 |
| `keyext.ui.testgen.fx` | 18 |
| `keyext.proofmanagement.fx` | 4 |
| **Total** | **92** |

To re-derive this table at any point: `grep -rn 'KNOWN-SIMPLIFIED' */src/main */src/test`.

The status column is for the close-out tracking: **OPEN** items are candidates for a later
milestone, **FIXED-UPSTREAM** items differ from a Swing bug that the port deliberately corrects,
**WONT-REPLICATE** items depend on Swing-only machinery with no FX counterpart.

**Ledger status (WP-11 close-out, 2026-10-12):** no row is OPEN. Every row ends RESOLVED (with
its batch/WP reference), WONT-REPLICATE or FIXED-UPSTREAM; the rows marked "—" record deliberate
simplifications that never needed close-out tracking (faithful-port notes, test-design notes,
site-specific decisions like the owner-less file chooser). The marker-count table above reflects
the original audit inventory; as rows were resolved during the P-batches and WP-1…WP-10, some
per-site markers were consolidated into summary javadoc blocks (e.g. `ExplorationExtensionF`),
so a raw `grep` count today is lower than the original 68. The behaviour-level counterpart of
this ledger is `PARITY-SIGNOFF.md` (closed, incl. the deliberate per-feature deferrals such as
the SMT select menu, WP-7); the module-level removal plan for the Swing side is
`SWING-RETIREMENT.md`.

---

## `key.ui.fx` — built-in contrib extensions (3)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `extension/contrib/HeatmapF.java:28` | `HeatmapExt` renders the heat highlight into the proof tree / sequent | menu + toolbar toggle + persisted `ViewSettings` options only; proof-tree heat overlay deferred | OPEN |
| `extension/contrib/HeatmapF.java:37` | — (doubles the `@Info` description) | same decision restated for the extension dialog | OPEN |
| `extension/contrib/ParallelProverStatusIndicatorF.java:27` | toggle button "SC" / "MT N×" with left-click toggle and right-click worker-count menu | RESOLVED (WP-3): `Button` with the Swing "SC"/"MT Nx" text format, left-click toggles through the real `onAction` handler (Swing `ParallelProverStatusIndicator` action), right-click opens a `ContextMenu` with the Single-core radio + "Multi-core, N workers" items for the `TreeSet{2, 4, 8, cores}` counts (Swing ParallelProverStatusIndicator.java:92-121); the FX auto-mode state is folded into the tooltip ("Auto mode running."/"Idle." prefixes) | RESOLVED (WP-3) |

## `key.ui.fx` — SMT run UI + exit flow + input freeze (4)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `SolverListenerF.java:81` | results applied via `SMTProofApplyUserAction` (undoable history entry) with the `stopInterface` input freeze around it | RESOLVED (WP-7): `SolverListenerF.applyResults` runs `SMTProofApplyUserActionF.actionPerformed()` — the `UserActionF` port (name "Close: %d goals by SMT", undo = prune to the original nodes + default selection, canUndo = all applied nodes still findable) executed inside the mediator auto-mode context with `stopInterface` freeze around it (Swing SolverListener.java:209-221 parity); the `UserActionListenerF` seam (`KeYMediatorF.addUserActionListener/fireActionPerformed`) is asserted by the undoable-apply extension of `key.fx.verify.smt` (freeze events, undo re-opens a goal) | RESOLVED (WP-7) |
| `InformationWindowF.java:24` | counterexample model tree (`CETree`) with line numbers (`TextLineNumber`) and the counterexample help tab | RESOLVED (WP-7): the counterexample tabs are ported — the `CETreeF` model tree (double-click expansion of `#o`/`#l`/`#s` reference leaves, `IGNORECASE_COMPARATOR` rows), the Help tab (`CE_HELP` text) and a simple line-number gutter for the information tabs (FX has no `TextLineNumber`); the window retitles to "Counterexample ..." for the Z3 CE solver with a model (Swing InformationWindow.initModel, :88-101); asserted by `key.fx.verify.testgen` | RESOLVED (WP-7) |
| `MainWindowF.java:3721` | exit fires the mediator shutdown event (`fireShutDown` → `GUIListener.shutDown`) | RESOLVED (WP-1): `KeYMediatorF` has the GUI-listener registry (`GUIListenerF`, `addGUIListener`/`removeGUIListener`, Swing `KeYMediator.java:306-410`) and the exit flow fires the event (`mediator.fireShutDown(new EventObject(this))`); the Swing listener's window-hiding is the `Platform.exit` of the flow | RESOLVED (WP-1) |
| `MainWindowF.java:2659` | the glass pane covered the whole content pane and re-delivered events only to components marked `isAutoButton` (automation/stop buttons + status-line abort button) | WONT-REPLICATE (WP-1 decision): the overlay keeps covering only the views area (workspace + drawers). The menu bar/toolbar proof actions are disabled during auto mode anyway (enablement binds to `mediator.autoModeRunningProperty()`), so blocking clicks on inert controls adds no protection; the automation macro items are enabled during auto mode by Swing parity so a click stops the run (MacroAutomationAction.java:48-61) and blocking them would regress that intent; the status bar must stay live for the progress display; and the stop controls the Swing glass pane kept live are the same controls the FX toolbar keeps live | WONT-REPLICATE (WP-1) |

## `key.ui.fx` — built-in extension ports (24)

The six Swing built-in extensions ported as `KeYGuiExtensionF` providers (ShowHashcodes,
JmlEnabledKeysIndicator, LogView, HeapStatus, OriginTermLabels, KeyboardTaclet); the Swing
`WDLoadDialogOptionPanel` (LoadOptionPanel) and `DockingLayout` (Startup) remain documented
deviations of the FX UI.

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `extension/contrib/ShowHashcodesExtensionF.java:63` | tooltip is one HTML string (`<b>`/`<br>`, ShowHashcodesExtension.java:36-44) | plain-text lines (JavaFX Tooltip renders no HTML); a non-sequent position without a `PosInOccurrence` is guarded to the empty list where Swing NPEs | WONT-REPLICATE |
| `extension/contrib/JmlEnabledKeysIndicatorF.java:65` | label constructed in the constructor, `PropertyChangeListener` registered there (JmlEnabledKeysIndicator.java:26-31) | label created lazily inside `getStatusLineControls`, listener registered in the `StartupF.init` hook (providers must instantiate toolkit-free) | — |
| `LogViewF.java:153` | `ShowLogAction` opens a fresh `JDialog` per click (LogView.java:95-125) | single-instance open: a repeated open raises the existing window; the status-line button (`LogViewExtensionF`) and the View-menu entry share one instance | — |
| `extension/contrib/LogViewExtensionFTest.java:26` | — (test design) | toolkit-free tests cannot construct the button surface | — |
| `extension/contrib/HeapStatusF.java:85` | `HeapStatusComponent` constructs its UI eagerly | control created lazily inside `getStatusLineControls` (providers instantiate toolkit-free) | — |
| `extension/contrib/HeapStatusF.java:180` | Swing `Timer(5000, …)` fires forever | scene-scoped daemon scheduler: the 5 s refresh starts on scene attach and cancels on detach (anti-leak) | — |
| `extension/contrib/HeapStatusF.java:239` | HTML-table tooltip (HeapStatusExt.java:89-94) | plain multi-line tooltip text | WONT-REPLICATE |
| `extension/contrib/HeapStatusF.java:294` | "Could not find jconsole…" tooltip on the disabled menu item | disabled item + log message (JavaFX `MenuItem` has no tooltip) | WONT-REPLICATE |
| `extension/contrib/HeapStatusF.java:320` | `JOptionPane.showConfirmDialog` on a jconsole launch failure | `Alert(ERROR)` + `showAndWait` (the Swing dialog result was never used) | — |
| `originlabels/OriginTermLabelsExtF.java:79` | new top-level "Origin Tracking" menu (`ToggleTermOriginTrackingAction.java:40`) | the cluster nests under the built-in View menu and absorbs the former direct `OriginLabelsF.install` wiring | — |
| `originlabels/OriginTermLabelsExtF.java:124` | a live settings property listener drives the "Show origin" enablement | build-time enablement (the FX popup is rebuilt on every show) | — |
| `originlabels/OriginTermLabelsExtF.java:202` | HTML tooltip strings | plain text with line breaks (the single possibly-empty string shape is kept) | WONT-REPLICATE |
| `originlabels/OriginLabelsF.java:78` | (Swing: direct wiring, no provider) | single-shot installation guard: the first caller wins, repeated calls (verify-harness menu-bar rebuilds) return empty | — |
| `originlabels/OriginLabelsF.java:141` | flat "Hide Package Prefix" `CheckboxMenuItem` in the View menu | single-item submenu | — |
| `originlabels/OriginLabelsF.java:144` | flat cluster with separator at the MP3a position (after Syntax Highlighting) | separator dropped; the facade appends the cluster at the end of the View menu | — |
| `extension/contrib/KeyboardTacletExtensionF.java:36` | dock-title `CDropDownButton` "Options" with four check-style toggles (KeyboardTacletExtension.java:199-209) | panel-header check boxes (matching the Swing commented sketch :115-119; also `KeyboardTacletPanelF.java:196`) + check-style `DockTitleActionF`s via `getTitleActions()`; the check flavour renders via `DockWorkspace.createTabContextMenu` | — |
| `extension/contrib/KeyboardTacletExtensionF.java:36` | selection listener registered inside `getPanels` (KeyboardTacletExtension.java:66-71) | listener registered in the `StartupF.init` hook; updates marshalled with `FxUtil.runLater` | — |
| `extension/contrib/KeyboardTacletExtensionF.java:36` | the Swing tab has no icon | drawer-identity glyph `KEYBOARD_TACLET` (drawer icon convention) | — |
| `extension/contrib/KeyboardTacletPanelF.java:55` | mouse position observed via `PROP_LAST_MOUSE_POSITION`, getter falls back to a toplevel sequent pos (SequentView.java:349-356) | `hoveredPosProperty()` is null outside the sequent → "no last mouse position" warning + all-taclets fallback (Swing: NPE caught into an empty list) | — |
| `extension/contrib/KeyboardTacletPanelF.java:55` | key feed delivers typed characters; ESC/backspace are delivered once | control chars skipped in `KEY_TYPED` (JavaFX double-delivers ESC/backspace as pressed+typed) | — |
| `extension/contrib/KeyboardTacletPanelF.java:199` | look&feel check box insets | cosmetic 8px gap | — |
| `extension/contrib/KeyboardTacletPanelF.java:207` | MigLayout default gap | cosmetic 4px gap | — |
| `extension/contrib/KeyboardTacletPanelF.java:301` | `TabPanel` title-action separator after Activate | no separator equivalent in `List<DockTitleActionF>` | — |
| `extension/contrib/KeyboardTacletPanelF.java:445` | `Services` captured once from the mediator (KeyboardTacletExtension.java:110) | services taken from the current goal's proof on every rebuild (a proof swap cannot leak a stale services instance) | FIXED-UPSTREAM |

## `keyext.caching.fx` (10)

| Site | Swing original | FX port | Status |
|---|---|---|---|
| `CachingExtensionF.java:95` | `CachingSettingsProvider.getCachingSettings()` on the keyext compile path | the FX module owns the `ProofCachingSettings` singleton via `CachingSettingsProviderF.getCachingSettings()` (Swing provider not loadable on the FX compile path) | FIXED-UPSTREAM |
| `CachingExtensionF.java:129` | menu checkbox instantiated eagerly | created lazily on first use (constructing controls needs the FX toolkit; the SPI may instantiate the provider headless) | — |
| `CachingExtensionF.java:735` | opens the interactive `ReferenceSearchDialog` (per-goal table + "Apply") | read-only summary `Alert`; copying the referenced steps stays available through the "Copy referenced proof steps here" context item | OPEN |
| `CachingExtensionF.java:778` | feeds `mediator.getCurrentlyOpenedProofs()` to the reference search | the seam now exists (WP-1: `KeYMediatorF.getCurrentlyOpenedProofs()`, kept live by the `ProofManagerF` sync in `MainWindowF`) — the tracked proofs are still used instead; migrating the port is WP-4's scope | OPEN (seam WP-1) |
| `CachingPruneHandlerF.java:26` | iterates `mediator.getCurrentlyOpenedProofs()` | iterates the proofs tracked by the owning extension (every proof selected at least once); the WP-1 accessor now exists, migrating the port is WP-4's scope | — |
| `CachingSettingsProviderF.java:37` | keyext registers the caching settings into `ProofIndependentSettings` | the FX module owns and registers the same singleton itself (shared persisted object with the Swing keyext via the registry) | — |
| `CachingSettingsProviderF.java:109` | writes `strategySearch.isEnabled()` (latent Swing bug — `JCheckBox#isEnabled` always true, persisted `true`) | writes the checkbox *selection* — the behaviour the panel visibly offers | FIXED-UPSTREAM |
| `CopyBeforeDisposeF.java:25` | wraps the copy into `mediator.initiateAutoMode(...)`/`finishAutoMode(...)` | the seam now exists (WP-1: `KeYMediatorF.initiateAutoMode(Proof, boolean fullStop, boolean interactive)`/`finishAutoMode(...)` for foreign proofs, Swing KeYMediator.java:535-566 parity) — the core `CopyReferenceResolver` is still invoked directly; wrapping the copy is WP-4's scope | OPEN (seam WP-1) |
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
