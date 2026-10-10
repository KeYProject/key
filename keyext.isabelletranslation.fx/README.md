# keyext.isabelletranslation.fx — JavaFX port of the Isabelle translation extension (MP9.3)

JavaFX port of `keyext.isabelletranslation` on the [`KeYGuiExtensionF`](../key.ui.fx/src/main/java/de/uka/ilkd/key/gui/fx/extension/api/KeYGuiExtensionF.java)
SPI. *"Isabelle Translation"* — translate the sequent of the selected goal into an Isabelle theory.

## Capabilities

Implements `SettingsF`, `ContextMenuF`, `StartupF` (service-loaded, `@Info(name = "Isabelle
Translation", optional = true)`).

| Piece | Class | Notes |
|---|---|---|
| Extension provider | `IsabelleTranslationExtensionF` | sequent context items "Translate goal to Isabelle theory" (selected goal / whole goal), settings integration |
| Runner | `IsabelleTranslationRunnerF` | runs `IsabelleTranslator.translateProblem` (shared with Swing) on a background thread and shows the theory text |
| Dialog | `IsabelleTranslationDialogF` | plain dialog displaying the generated theory |
| Settings | `IsabelleSettingsProviderF` | Isabelle path / translation path / timeout; key constants mirrored (package-protected in keyext) |

## Verification

In-app (needs a display): right-click a sequent term → "Translate…", or use the Settings dialog
category "Isabelle Translation". No external Isabelle solver is launched.

## Tests

`IsabelleTranslationExtensionFTest` — fully toolkit-free: `@Info` metadata, SPI null guards and
the two translate context items for a real (headless-loaded) goal. The settings-panel surface is
covered by `IsabelleSettingsProviderFTest`, which starts the FX toolkit and **skips** on headless
CI runners (no display) via JUnit assumptions; the panel itself is verified in-app.

## Known simplifications

Full ledger: [KNOWN-SIMPLIFIED.md](../key.ui.fx/KNOWN-SIMPLIFIED.md) § keyext.isabelletranslation
(4 rows). Highlight: the Swing actions hand the theory to the external Isabelle solver with a
progress/model dialog; the FX port stops after the translation itself and never loads the heavy
scala-isabelle backend (`IsabelleTranslationExtensionF.java:37`, `IsabelleTranslationRunnerF.java:28`).
