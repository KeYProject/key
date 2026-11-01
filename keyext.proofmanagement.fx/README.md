# keyext.proofmanagement.fx — JavaFX port of the proof-management extension (MP9.6)

JavaFX port of `keyext.proofmanagement` on the [`KeYGuiExtensionF`](../key.ui.fx/src/main/java/de/uka/ilkd/key/gui/fx/extension/api/KeYGuiExtensionF.java)
SPI. *"Proof management"* — run soundness checks on proof bundles (missing proofs, settings,
replay, dependency checkers) and generate an HTML report.

## Capabilities

Implements `MainMenuF` (service-loaded, `@Info(name = "Proof management", optional = true)`);
`@NullMarked`.

| Piece | Class | Notes |
|---|---|---|
| Extension provider | `ProofManagementExtF` | contributes the **Proof Management** menu (`MENU_PM`, matching the Swing menu text) |
| Check configuration dialog | `CheckConfigDialogF` | selects checkers, the proof bundle (`.zproof`) and the report location, then runs the checkers in the background via the unchanged `Main.CheckCommand`; input controls are disabled while the check runs ("Run checkers" → "Stop"); outcome alert |

## Verification

In-app (needs a display): the Proof Management menu appears in the menu bar; run a check against
a proof bundle and confirm the report path handling (HelpFacade seam) and the result alert.

## Tests

`ProofManagementExtFTest` — toolkit-free provider/annotation surface.

## Known simplifications

Full ledger: [KNOWN-SIMPLIFIED.md](../key.ui.fx/KNOWN-SIMPLIFIED.md) § keyext.proofmanagement
(4 rows). Highlights: the Swing `BlockingGlassPane` is replaced by explicit control disabling
(`CheckConfigDialogF.java:45`); AWT `KeYFileChooser` filters become FX `FileChooser` extension
filters (`CheckConfigDialogF.java:50`); the report opens through the `HelpFacadeF` browser seam
rather than `Desktop.getDesktop().open` (`CheckConfigDialogF.java:55`).
