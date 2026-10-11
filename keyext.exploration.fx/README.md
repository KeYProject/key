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
| Extension provider | `ExplorationExtensionF` | registers the `ExplorationModeModel` in the mediator registry (WP-5, Swing `mediator.register` parity) with the provider-held singleton as lookup fallback; toggle + sequent menu + status entry; hides justification through the `ProofTreeViewF` `HIDE_INTERACTIVE_GOALS` filter (WP-5) |
| Proof-tree renderer | `ExplorationRendererF` | purple border/background + "Exploration Action Performed" tooltip on explored branches via the `ProofTreeViewF.CellStyler` hook (WP-5, Swing `ExplorationRenderer` parity); colors behind the shared `[proofTree]darkPurple`/`lightPurple` keys |
| Exploration Steps panel | `ExplorationStepsPanelF` | west-drawer left panel (add/edit/hide steps, prune, live sequent integration) |
| Sequent context menu | `ExplorationSequentMenuF` | "Generate Exploration Step" etc.; `promptForTerm` modal retry-loop ported (WP-5, Swing `ExplorationAction.promptForTerm` parity; `PromptHandler` seam for headless tests) |
| Status indicator | (in provider) | ikonli FontAwesome solid vs. regular compass mirrors the Swing `Icons.EXPLORE` |

## Verification

In-app (needs a display): `key.fx.verify.extensions` expects the panel on the west drawer
(`westDrawerItems=7`); `key.fx.verify.exploration` (WP-5) asserts the model registration via the
mediator lookup, the purple renderer border on a real exploration step of the demo, the
hide-justification tree-filter routing and the promptForTerm bad-then-good retry. Toggle
exploration mode from the toolbar/status entry, add an exploration step on the sequent and check
the panel collects it.

## Tests

`ExplorationExtensionFTest` — toolkit-free provider/annotation surface.

## Known simplifications

Full ledger: [KNOWN-SIMPLIFIED.md](../key.ui.fx/KNOWN-SIMPLIFIED.md) § keyext.exploration (9 rows).
Highlights: proof-tree styling (`ExplorationRenderer`) and the hidden second-branch tree filter
have no FX seam and are dropped (`ExplorationExtensionF.java:54,363`); the term prompt is
single-shot instead of the Swing retry-loop (`ExplorationSequentMenuF.java:48`).
