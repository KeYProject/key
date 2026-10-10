# key.ui.fx — the JavaFX user interface of KeY

`key.ui.fx` is the JavaFX re-implementation of the Swing GUI (`key.ui`) of the interactive
theorem prover KeY. It is built in pure JavaFX code:

* **no FXML** — every view is constructed in code,
* **no AWT/Swing imports** — the module never references `java.awt` or `javax.swing`,
* icons use the [ikonli](https://kordamp.org/ikonli) FontAwesome family (no Unicode glyph
  fallbacks),
* JavaFX is consumed through the Gradle `openjfx` plugin (`javafx.base`, `javafx.controls`,
  `javafx.graphics`, `javafx.web`).

The SMT-relevant and proof machinery is reused unchanged from `key.core`; only the GUI layer is
rewritten.

## Running

```sh
./gradlew :key.ui.fx:run        # the full application (MainEx)
./gradlew :key.ui.fx:runExperimental
./gradlew :key.ui.fx:runDebug
```

Additional Gradle tasks come from the `application` plugin; `key.fx.*` system properties are
forwarded to the application JVM by the `run` task (whitelist) or via `JAVA_TOOL_OPTIONS` (see
below).

JavaFX 25 silently drops machines without a graphical environment; for headless runs use a
virtual display (Xvnc/Xvfb), e.g. `DISPLAY=:99`, and `-Dprism.order=sw`.

> **Packaging note (M0):** a JavaFX application does not assemble into a plain fat jar by
> shading bytecode — the platform-specific native runtime comes from classifier jars and must be
> bundled with jlink/jpackage. Until that milestone, run via `./gradlew :key.ui.fx:run`.

## Headless app-verification (`key.fx.verify.*`)

The application carries self-test hooks that run after a demo proof is loaded and print
`PASS`/`FAIL` markers on stdout with `System.exit` semantics — this is how the whole GUI is
regression-tested on a virtual display. Demo proof paths default into
`key.ui/examples/` (e.g. `firstTouch/01-Agatha/project.key` or
`standard_key/queries/useQuery.key` for `updatehighlight`).

| Flag | What it verifies |
|---|---|
| `key.fx.demo.sequent=<file.key>` | demo proof to load (most hooks require one) |
| `key.fx.demo.sequent2` / `key.fx.demo.sequent3` | second/third loaded proof (Loaded Proofs view test) |
| `key.fx.demo.proofmgmt=<file.key>` | example for the proof management dialog test |
| `key.fx.show=sequent\|prooftree` | dockable focused after the demo load |
| `key.fx.theme=light\|dark` | theme override |
| `key.fx.demo.autoprove` / `key.fx.demo.autoprove.live` / `key.fx.demo.maxsteps=n` | auto-mode behaviour, live refresh, step limit |
| `key.fx.verify.sequent` | sequent text → `PosInOccurrence` position mapping |
| `key.fx.verify.tree` | proof-tree structure model |
| `key.fx.verify.goallist` | goal-list view after the demo load |
| `key.fx.verify.search` | proof-tree search self test |
| `key.fx.verify.sequentsearch=q` | sequent search with query `q` |
| `key.fx.verify.sequentsearchmodes` | search modes (Highlight / Hide / Regroup) |
| `key.fx.verify.treefilters` | tree filters after auto mode |
| `key.fx.verify.updatehighlight` | update-highlight overlay (needs `useQuery.key`) |
| `key.fx.verify.notifications` | notification framework (task-finished, proof-closed, exception) |
| `key.fx.verify.termmenu` | headless sequent context-menu model (25 checks) |
| `key.fx.verify.sequentmenu` | left-click sequent term menu + POPUP_DELAY guard, search prefill, shift+click focussed auto mode (P2a) |
| `key.fx.verify.dialogs` | contract-completion registry + dialog skeletons (P2b): contract/auxiliary configurators, lemma selection dialog, item chooser |
| `key.fx.verify.tacletmatch=1\|hold` | interactive taclet application (`hold` keeps the dialog open) |
| `key.fx.verify.uicontrol` | `WindowUserInterfaceControlF` seam: status line, IssueDialogF, LogViewF, AutoDismissDialogF |
| `key.fx.verify.docking` | named layout slots, maximize/restore, close-while-maximized |
| `key.fx.verify.proofmgmt=1\|2\|all` | ProofManagementDialogF / Loaded Proofs view |
| `key.fx.verify.joinmerge` (+ `key.fx.verify.joinmerge.maxsteps=n`) | join/merge dialogs on a proof with open branches |
| `key.fx.verify.lemmaorigin` | term labels, origin labels, lemma generator |
| `key.fx.verify.help` | F1 context-help resolution (no browser window) |
| `key.fx.verify.soundiness` | soundiness report dialog |
| `key.fx.verify.profileloading` | WD loading-options panel |
| `key.fx.verify.profileloadingdialog` | loading options dialog at startup |
| `key.fx.verify.javacsettings` | javac settings provider |
| `key.fx.verify.colors` | colors palette: Swing-parity property count, mapped CSS-variable wiring, override round trip |
| `key.fx.verify.smt` | SMT run UI end to end (needs an installed solver, e.g. `z3` on the `PATH`): launches the union on the demo goal, auto-applies the result, checks the closed goal |
| `key.fx.verify.loadingexit` | loading/exit: recent-files store round trip with loading options + profile resolution (snapshot/restore), then the window close button path — the process must terminate with exit code 0 |
| `key.fx.verify.shortcuts` | shortcuts: Swing-parity defaults, no binding collisions, an override round trip, and the sequent view Ctrl+F key path |
| `key.fx.verify.inputfreeze` | input freeze: the auto-mode blocking overlay — direct freeze/unfreeze with key blocking, then an auto-mode-driven run |

Harness-injected flags (read in `MainWindowF` but not on the `run`-task whitelist; the
verification harness sets them via `JAVA_TOOL_OPTIONS`):

| Flag | What it verifies |
|---|---|
| `key.fx.verify.extensions` | extension SPI discovery: `discovered=9` (3 built-in + 6 keyext), `statusControls=7`, `westDrawerItems=7` |
| `key.fx.verify.drawerlayout` | west drawer round trip (`west = 5 + facade left-panel tabs`) |
| `key.fx.verify.drawer` | drawer switch/move interactions |
| `key.fx.verify.menuparity` | menu parity counts (File 16 / Proof 24 / Options 12 / View 7 / About 5) |
| `key.fx.verify.rightclickmacro` | right-click macro menu |
| `key.fx.verify.minimizeinteraction` | minimize-interaction toggle |
| `key.fx.verify.autosave` | auto saver |
| `key.fx.verify.proofdiff` | proof-diff frame |

**Regression practice (S5/MP10 mode):** run the hooks **per flag** — a combined multi-flag run
stalls at the `uicontrol` modal (the seam dialog needs an XTEST Return/Escape dismissal, see
`/tmp/opencode/xsendkey`). `uicontrol` is run separately and dismissed with the synthetic key.

## Architecture

* `MainWindowF` — the window shell: `top` = menu/toolbar, `center` = docking workspace wrapped
  in WEST/EAST/SOUTH `DrawerF`s, `bottom` = status line. Menu parity with the Swing app is
  checked by `key.fx.verify.menuparity`.
* `DockWorkspace` + `Dockable` — the docking framework with persisted layouts
  (`DockLayoutStore`), named layout slots (F10–F12), maximize/restore and title actions.
* `KeYMediatorF` / `KeYSelectionModel` — selection + auto-mode event hub mirroring the Swing
  mediator; `WindowUserInterfaceControlF` is the `UserInterfaceControl` seam for
  status/progress/task/exception callbacks and interactive rule application.
* `nodeviews` — proof tree, sequent view (`TextFlow` + the shared `pp` printer), source view
  (RichTextFX), goal list, search bars, term context menu (`SequentTermContextMenuF` +
  `SequentMenuModelF`).
* `settings` — the Settings dialog framework (`SettingsManagerF`, `SettingsProviderF`) and
  `Configuration` round trips.
* `colors` / `configuration` — `ColorSettingsF` / `ConfigF` theme plumbing.

## Extension SPI

`extension.api.KeYGuiExtensionF` (mirror of the Swing `KeYGuiExtension`) is the JavaFX extension
contract; capability interfaces: `MainMenuF`, `ToolbarF`, `StatusLineF`, `ContextMenuF`,
`SettingsF`, `StartupF`, `LeftPanelF`. Providers are discovered by `ServiceLoader` through
`KeYGuiExtensionFacadeF`.

* Built-in providers in `extension/contrib`: `HeatmapF`, `ParallelProverStatusIndicatorF`,
  `ProfileNameInStatusBarF`.
* The six keyext extensions are ported as modules and attached `runtimeOnly`:
  `keyext.caching.fx`, `keyext.exploration.fx`, `keyext.isabelletranslation.fx`,
  `keyext.slicing.fx`, `keyext.ui.testgen.fx`, `keyext.proofmanagement.fx`
  (see the per-module READMEs).

## Tests & CI

* Unit tests are deliberately **toolkit-free** (JavaFX 25 throws "Toolkit not initialized" when
  a `Control` is constructed headless): they assert the pure-Java model (e.g.
  `SequentMenuModelFTest`) and the provider/capability surface of each keyext module. The
  control-level behaviour is covered by the `key.fx.verify.*` hooks instead.
* Per-commit gate: `./gradlew --no-daemon :key.ui.fx:spotlessApply :key.ui.fx:compileJava
  :key.ui.fx:test`.
* CI: the FX modules are part of the `tests.yml` unit-test matrix, the `spotlessCheck` quality
  job and the broad release-test `test` runs. The **whole build targets JDK 25** (JavaFX 25 jars
  are class-file version 67 = JDK 23+); the CI matrices use Corretto/Temurin 25 accordingly.

## Documents

* `KNOWN-SIMPLIFIED.md` — the consolidated ledger of every deliberate deviation from the Swing
  originals (all `KNOWN-SIMPLIFIED` markers, one row per site).
* `PARITY-SIGNOFF.md` — sign-off of the 2026-10-08 parity audit (~490 behaviors) against the
  delivered application, and the list of still-open items.
