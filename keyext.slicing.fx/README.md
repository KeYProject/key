# keyext.slicing.fx — JavaFX port of the proof-slicing extension (MP9.4)

JavaFX port of `keyext.slicing` on the [`KeYGuiExtensionF`](../key.ui.fx/src/main/java/de/uka/ilkd/key/gui/fx/extension/api/KeYGuiExtensionF.java)
SPI. *"Slicing"* (port by Arne Keller) — analyze proofs to remove useless rule applications and
replay the sliced proof.

## Capabilities

Implements `ContextMenuF`, `StartupF`, `LeftPanelF`, `SettingsF` (service-loaded,
`@Info(name = "Slicing", optional = true, priority = 9001)`); `@NullMarked`.

| Piece | Class | Notes |
|---|---|---|
| Extension provider | `SlicingExtensionF` | sequent context items ("Slice proof", "Show dependency graph around this formula", "Analyze proof"), proof-load tracking via `KeYSelectionListener` |
| Left panel | `ui/SlicingLeftPanelF` | west-drawer panel: slice / slice-to-fixed-point, analyze, rule statistics, execution timings, DOT export/rendering, load sliced proof |
| Settings | `SlicingSettingsProviderF` | per-algorithm toggles, DOT executable; the aggressive-deduplicate flag is read-only (package-private setter in keyext) |

## Verification

In-app (needs a display): `key.fx.verify.extensions` expects the panel on the west drawer
(`westDrawerItems=7`); right-click a sequent term → "Slice proof" on a proof with several
branches; check the sliced proof loads.

## Tests

`SlicingExtensionFTest` — toolkit-free provider/annotation surface (widget contributions are
verified in-app).

## Known simplifications

Full ledger: [KNOWN-SIMPLIFIED.md](../key.ui.fx/KNOWN-SIMPLIFIED.md) § keyext.slicing (16 rows).
Highlights: graphviz rendering and the HTML table dialogs become DOT/text dialogs
(`SlicingLeftPanelF.java:322,295,464`); "slice to fixed point" performs a single iteration
(`SlicingLeftPanelF.java:222`); sliced proofs register in the recent-files list
(`SlicingLeftPanelF.java:415`).
