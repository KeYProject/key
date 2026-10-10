# keyext.exploration.fx — JavaFX port of the exploration extension (MP9.2)

JavaFX port of `keyext.exploration` on the [`KeYGuiExtensionF`](../key.ui.fx/src/main/java/de/uka/ilkd/key/gui/fx/extension/api/KeYGuiExtensionF.java)
SPI. *"Exploration"* (experimental) — add, edit and hide formulas on the sequent with
sound-cut-based exploration steps and collect them in the "Exploration Steps" panel.

## Capabilities

Implements `ToolbarF`, `MainMenuF`, `StatusLineF`, `LeftPanelF`, `ContextMenuF`, `StartupF`
(service-loaded, `@Info(name = "Exploration", experimental = true, optional = true,
priority = 10000)`).

| Piece | Class | Notes |
|---|---|---|
| Extension provider | `ExplorationExtensionF` | holds the `ExplorationModeModel` directly (no mediator registry on the FX side); toggle + sequent menu + status entry; hides justification via `ViewSettings` |
| Exploration Steps panel | `ExplorationStepsPanelF` | west-drawer left panel (add/edit/hide steps, prune, live sequent integration) |
| Sequent context menu | `ExplorationSequentMenuF` | "Generate Exploration Step" etc.; single-shot term prompt (Swing retry-loop simplified) |
| Status indicator | (in provider) | ikonli FontAwesome solid vs. regular compass mirrors the Swing `Icons.EXPLORE` |

## Verification

In-app (needs a display): `key.fx.verify.extensions` expects the panel on the west drawer
(`westDrawerItems=7`); toggle exploration mode from the toolbar/status entry, add an exploration
step on the sequent and check the panel collects it.

## Tests

`ExplorationExtensionFTest` — toolkit-free provider/annotation surface.

## Known simplifications

Full ledger: [KNOWN-SIMPLIFIED.md](../key.ui.fx/KNOWN-SIMPLIFIED.md) § keyext.exploration (9 rows).
Highlights: proof-tree styling (`ExplorationRenderer`) and the hidden second-branch tree filter
have no FX seam and are dropped (`ExplorationExtensionF.java:54,363`); the term prompt is
single-shot instead of the Swing retry-loop (`ExplorationSequentMenuF.java:48`).
