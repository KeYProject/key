# keyext.caching.fx — JavaFX port of the proof-caching extension (MP9.1)

JavaFX port of `keyext.caching` on the [`KeYGuiExtensionF`](../key.ui.fx/src/main/java/de/uka/ilkd/key/gui/fx/extension/api/KeYGuiExtensionF.java)
SPI. *"Proof Caching"* — functionality related to reusing previous proof results in similar
proofs: reference search across closed proofs, copy-before-dispose, copy-on-prune.

## Capabilities

Implements `MainMenuF`, `ToolbarF`, `StatusLineF`, `ContextMenuF`, `SettingsF`, `StartupF`
(service-loaded, `@Info(name = "Proof Caching", optional = true)`).

| Piece | Class | Notes |
|---|---|---|
| Extension provider | `CachingExtensionF` | menu checkbox, toolbar toggle, status button, sequent context items ("Copy referenced proof steps here"), automatic reference search |
| Copy-on-dispose listener | `CopyBeforeDisposeF` | runs the shared `CopyReferenceResolver` (Swing auto-mode shell not needed on the FX mediator) |
| Copy-on-prune handler | `CachingPruneHandlerF` | copies referenced steps over pruned branches from the proofs tracked by the extension |
| Settings | `CachingSettingsProviderF` | FX-module-owned `ProofCachingSettings` singleton, registered into `ProofIndependentSettings` |
| Status button | `CachingStatusButtonF` | status-line entry with ikonli FontAwesome icons |

## Verification

In-app (needs a display): run the app on Xvnc and check the extension list (`key.fx.verify.extensions`
expects `discovered=9`, `statusControls=7`); toggle the caching checkbox, use the sequent context
item, then open the settings category "Proof Caching".

## Tests

`CachingExtensionFTest` — toolkit-free: `@Info` annotation, capability surface, sequent-context
null guards, the module-owned settings singleton identity and registry idempotence, and the
service-loader registration file.

## Known simplifications

Full ledger: [KNOWN-SIMPLIFIED.md](../key.ui.fx/KNOWN-SIMPLIFIED.md) § keyext.caching (10 rows).
Highlights: the interactive `ReferenceSearchDialog` becomes a read-only summary alert
(`CachingExtensionF.java:735`); open proofs come from the FX-tracked selection instead of
`mediator.getCurrentlyOpenedProofs()`; the Swing settings write (`strategySearch.isEnabled()`) was
a latent bug the FX port drops.
