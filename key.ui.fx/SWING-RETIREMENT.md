# Swing retirement checklist — `key.ui` + the Swing `keyext.*` modules

**Status: PLAN ONLY — nothing here has been executed.** This document is the staged removal
plan required by WP-11 deliverable 3. The Swing UI keeps shipping unchanged until the
maintainers make the phase-3 decision (tracked as decision point 4 in `WORK-PACKAGES.md`):
removing `key.ui` and the Swing `keyext.*` modules is explicitly **not** part of the
Swing→JavaFX migration. This checklist records what that removal would involve, so the
decision can be made with facts on the table.

All numbers were taken at the WP-11 baseline `dd4afc56c1` (branch `weigl/ocfx`, 2026-10-12).

## 1. Inventory

### 1.1 Modules and sizes (main source sets)

| Module | Role | Files | Lines | JavaFX counterpart |
|---|---|---|---|---|
| `key.ui` | Swing GUI (`de.uka.ilkd.key.gui.*`), Swing mediator (`de.uka.ilkd.key.core.*`: `Main`, `KeYMediator`, …), headless controls (`de.uka.ilkd.key.ui.*`), examples (`key.ui/examples/`), Swing product packaging (shadowJar/slimJar/installDist) | 371 | 73,532 | `key.ui.fx` (complete) |
| `keyext.caching` | proof-caching extension (Swing) | 19 | 1,893 | `keyext.caching.fx` |
| `keyext.exploration` | exploration-mode extension (Swing) | 13 | 1,474 | `keyext.exploration.fx` |
| `keyext.isabelletranslation` | Isabelle translation extension (Swing) | 42 | 6,036 | `keyext.isabelletranslation.fx` |
| `keyext.slicing` | proof-slicing extension (Swing) | 37 | 6,231 | `keyext.slicing.fx` |
| `keyext.ui.testgen` | test-case generation extension (Swing) | 7 | 875 | `keyext.ui.testgen.fx` |
| `keyext.proofmanagement` | proof-management extension (Swing) | 26 | 4,132 | `keyext.proofmanagement.fx` |

**All six keyext extensions have complete JavaFX ports — none is unported.** The Swing
counterparts remain in the build for the Swing UI and as hosts of shared logic (see 1.2).

### 1.2 What `key.ui.fx` / `keyext.*.fx` still (compile-)couple to from the Swing side

Compile-classpath couplings (`grep -P '^\s*import de\.uka\.ilkd\.key\.gui\.'`, excluding the
modules' own `.fx` packages):

| Module | Swing `key.ui` class import sites | Detail |
|---|---|---|
| `key.ui.fx` | **0** | build.gradle declares no `:key.ui` dependency at all. Remaining references are non-code: javadoc "counter-part of `de.uka.ilkd.key.gui.X`" notes, the Swing action FQCN **strings** in the `KeyStrokeManagerF` defaults table (persisted `keystrokes.json` compatibility keys, not compiled references), and resources copied under the Swing resource paths `de/uka/ilkd/key/gui/images|help` (same classpath names as the Swing UI). |
| `keyext.caching.fx` | **6** | `ProofCachingSettings` ×5 + `CachingException` ×1 — but both classes are hosted in the Swing keyext module `keyext.caching` (package `de.uka.ilkd.key.gui.plugins.caching.*`), resolved through `implementation project(":keyext.caching")`. No Swing widget type. |
| `keyext.exploration.fx` | 0 | own package is `org.key_project.exploration.fx`; imports from `key.ui.fx` only |
| `keyext.isabelletranslation.fx` | 0 | own package is `org.key_project.isabelletranslation.fx` |
| `keyext.slicing.fx` | 0 | but build.gradle declares `implementation project(":key.ui")` — **classpath only**, to resolve `SlicingSettingsProvider` behind the shared slicing logic ("No Swing type is used in this module's code", build.gradle comment) |
| `keyext.ui.testgen.fx` | 0 | own package `de.uka.ilkd.key.gui.testgen.fx` imports `key.ui.fx` classes only |
| `keyext.proofmanagement.fx` | 0 | own package is `org.key_project.proofmanagement.fx` |

Module-graph couplings that the FX build inherits:

* every `keyext.*.fx` depends (`implementation`) on its Swing `keyext.*` counterpart for the
  shared extension logic, and the counterparts depend on `:key.ui` — so **the Swing `key.ui`
  jar and the Swing keyext jars sit on the FX runtime classpath transitively** (unused by FX
  code; the "key.ui transitively, accepted for the user-approved extension migration; the FX
  sources never import Swing" wiring of the MP9.x scaffold).
* `:key.ui.fx:run` sets `key.examples.dir = $rootDir/key.ui/examples` — the demo/example
  proofs of the FX verification hooks live in the Swing module's example tree. (The Swing UI
  example chooser reads the same directory.)
* the `keyext.*` Swing modules themselves import heavily from `key.ui`'s `de.uka.ilkd.key.gui`
  (5–22 distinct classes per module) — the shared-logic extraction in phase 2 has to reason
  about exactly those.

### 1.3 Swing-only code with no FX consumer

* `de.uka.ilkd.key.core.Main` (Swing entry point) and the Swing mediator stack
  (`KeYMediator`, `KeYSelectionModel`, `Watchdog`, `Log`); the FX counterparts are
  `MainEx`, `KeYMediatorF`, `KeYSelectionModel(F)`, `WatchdogF`/`Log` copies in `key.ui.fx`.
* `de.uka.ilkd.key.ui.*` (`AbstractMediatorUserInterfaceControl`,
  `ConsoleUserInterfaceControl`, …) — headless/console UI used by core tooling and tests.
* the entire Swing GUI package tree `de.uka.ilkd.key.gui.*` (~the bulk of the 73.5k lines).
* `key.ui`'s test sources (e.g. `ChaosMonkey`, `IssueDialogMessageTest`, `KeyboardTacletTest`,
  `RecentFileMenuTest`, …) and the product packaging tasks (`shadowJar`, `slimJar`,
  `installDist`, `distZip`) — all Swing-product-bound.

## 2. Staged removal plan (each item is an explicit maintainer decision)

### Phase 1 — docs default → FX *(executed by WP-11, this migration)*

* [x] Root `README.md`: `./gradlew :key.ui.fx:run` documented as the default entry point;
      `key.ui:run` demoted to "legacy" (still runnable, nothing removed).
* [x] Root `settings.gradle`: module comments state the default/legacy roles.
* [x] `key.ui.fx/README.md`: run tasks, `-DmainClass` ergonomics, the `key.fx.*` whitelist
      (53 properties) and the headless verify recipe documented.
* [x] Root `build.gradle` `start` helper task message points to `:key.ui.fx:run` (default)
      and `:key.ui:run` (legacy).
* **Decision point 1a** — release notes / homepage announcement that FX is the default UI
  (outside this repository; maintainer action).

### Phase 2 — extract the remaining shared core used by both UIs

The goal: after phase 2, no FX module needs `key.ui` or a Swing keyext on its classpath for
*code* reasons — only the Swing UI itself does.

1. **`ProofCachingSettings` + `CachingException` relocation** — the FX caching extension
   compiles against these two classes in `keyext.caching` (package
   `de.uka.ilkd.key.gui.plugins.caching.*`). Move them to a Swing-free home (e.g. a small
   `keyext.caching.core`-style module or `key.core`), repoint `keyext.caching.fx` (drop the
   `:keyext.caching` dependency) and let the Swing keyext consume it from there.
   *Decision point 2a: target module + up-front vs. at-retirement timing.*
2. **Slicing settings singleton** — `keyext.slicing.fx` keeps `implementation project(":key.ui")`
   solely to resolve `SlicingSettingsProvider` behind `org.key_project.slicing` logic.
   Extract the settings provider/accessor out of `key.ui` (upstream `keyext.slicing` change)
   so the FX module compiles Swing-free. Same package-private-setter issue as the WP-6
   WONT-REPLICATE rows (`SlicingSettingsProviderF.java:29/:144`) — one upstream change can fix
   both. *Decision point 2b: upstream keyext.slicing approval (already flagged in WP-6).*
3. **Per-keyext runtime decoupling** — today each `keyext.*.fx` drags its Swing counterpart
   (and `key.ui`) onto the FX runtime classpath via `implementation`. Options per module:
   (a) keep as-is (harmless, Swing providers not loaded by the FX service loader), or
   (b) split the shared logic into Swing-free modules now. *Decision point 2c: per module
   (a)/(b) — cost/benefit is small; (a) is acceptable indefinitely.*
4. **Examples directory** — move `key.ui/examples/` to a Swing-neutral location (e.g.
   `key.examples/` or a resources-only module) and repoint `key.examples.dir` in both run
   tasks, the FX verify-hook defaults and the docs. *Decision point 2d: timing (can be done
   before retirement; pure move).*
5. **Swing maintenance mode** — declare `key.ui` + Swing `keyext.*` bugfix-only (no features)
   in the docs/CI while FX is the default. *Decision point 2e: policy.*

### Phase 3 — retire `key.ui` + Swing `keyext.*` *(not before the decision below)*

**Decision point 3a (the gate):** when and whether to remove. Suggested preconditions:

* the FX UI has shipped as the default for at least one stable release;
* the FX product packaging (jlink/jpackage — the M0 packaging note in `key.ui.fx/README.md`)
  exists, so the Swing fat-jar/installDist path is no longer the only distributable;
* no Swing-only workflow remains that users depend on (each phase-2 item resolved or
  consciously dropped);
* the swing-retirement decision recorded in `WORK-PACKAGES.md` (decision point 4) is made by
  the maintainers.

Then, in order:

1. **Test migration first** — `key.ui/src/test` contains Swing GUI tests and proof-run
   infrastructure that may be the only coverage of some core behaviours; port or retire each
   test explicitly. *Decision point 3b: which tests move where.*
2. **`keystrokes.json` compatibility keys** — `KeyStrokeManagerF` (key.ui.fx) carries the Swing
   action FQCNs as *persisted setting keys*; removing Swing changes nothing for the FX
   (the strings are data), but any migration tooling for user preferences must be checked
   before deletion. *Decision point 3c: keep the string table as the FX default-key identity
   (recommended) or rename.*
3. **Remove the Swing keyext counterparts** once phase-2 items 1–3 are done (their logic is
   fully in the `.fx` modules / extracted shared modules).
4. **Remove `key.ui`** — drop it from `settings.gradle`, delete the sources, remove the root
   README/build references (`start` task text, packaging section), and re-home anything still
   needed (`de.uka.ilkd.key.ui.*` console controls → `key.core` or a tools module, if still
   used).
5. **Product packaging** — provide the release artifacts for `key.ui.fx` (jlink/jpackage,
   distribution zips, the `key-*-exe.jar` equivalents) before or with the removal.
6. **Docs/website** — update homepage, the book's UI chapters, and the release notes; retire
   the "legacy" run instructions from the root README (the last step of phase 1's demotion).

## 3. What this checklist deliberately does *not* do

* It does not schedule or execute any removal — phases 2/3 are decision points for the
  maintainers (WORK-PACKAGES.md, decision point 4).
* It does not track FX-vs-Swing feature parity — see `PARITY-SIGNOFF.md` (closed at WP-11)
  and `KNOWN-SIMPLIFIED.md`.
* It does not claim anything about the full regression sweep (WP-11 deliverable 1, run by the
  parent session; recorded separately).
