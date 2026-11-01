# keyext.ui.testgen.fx — JavaFX port of the KeY test-generation UI (MP9.5)

JavaFX port of `keyext.ui.testgen` on the [`KeYGuiExtensionF`](../key.ui.fx/src/main/java/de/uka/ilkd/key/gui/fx/extension/api/KeYGuiExtensionF.java)
SPI. *"Test case generation"* — generate JUnit test cases from the current proof, or search for a
counterexample, using the Z3 CE solver. The generation macros/loaders come from `key.core.testgen`.

## Capabilities

Implements `SettingsF`, `StatusLineF`, `MainMenuF` (service-loaded, `@Info(name = "Test case
generation", optional = false)`); `@NullMarked`. The `:key.core` dependency (added in the MP9.5
integration review) enables the real `MainMenuF` — a **"Test Case Generation"** menu with the two
Swing actions.

| Piece | Class | Notes |
|---|---|---|
| Extension provider | `TestgenExtensionF` | menu with "Generate tests…" (+ `SHORTCUT+T`, accelerator lives on the menu item) and "Search for counterexample…"; status-line `MenuButton` + two plain buttons |
| Generation flow | `TestGenerationTaskF` / `TestgenReflectionF` / `LogSinkF` | facade route into the `key.core.testgen` machinery via reflection; result logging |
| Run dialogs | `TestGenResultsDialogF` / `CounterExampleResultsDialogF` / `CounterExampleTaskF` | generated-files list + live log; SMT statistics and found/not-found outcome |
| Settings | `TestgenSettingsProviderF` | reflectively-dispatched proxy provider (the module cannot name `MainWindowF`); options live exclusively in the Settings dialog |

## Verification

In-app (needs a display): open the "Test Case Generation" menu (or press `SHORTCUT+T`), run
"Generate tests…" against a proof with an annotated problem, and check the run dialog's log and
generated-files list. Requires a Z3 CE-capable solver on the path.

## Tests

`TestgenExtensionFTest` — toolkit-free: `@Info`, capability surface (`MainMenuF` + `SettingsF` +
`StatusLineF`), settings-provider dispatch.

## Known simplifications

Full ledger: [KNOWN-SIMPLIFIED.md](../key.ui.fx/KNOWN-SIMPLIFIED.md) § keyext.ui.testgen (18 rows).
Highlights: the Swing `Toolbar`/`Startup` slots become status-line buttons and lazy window
capture through the settings panel (`TestgenExtensionF.java:59,72`); the Swing `SolverListener`
modal progress/model dialogs become log output (`TestgenReflectionF.java:220`); stopping
interrupts the worker thread instead of a cooperative `StopRequest` (`TestGenerationTaskF.java:19`).
