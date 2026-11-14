# Plan: JSpecify nullness annotations for the KeY project

Applies the `jspecify-nullness` skill to the KeY project. Continues the goal of
PR #3470 ("Nullness Type System for `key.core`"), which failed because the EISOP
Checker Framework NullnessChecker was too slow over the whole module.
**Scope: every module, following the dependency chain and module size. Inside
modules, package by package.**

## Status

**✅ COMPLETE (PR #4003).** Every module is annotated and NullAway-clean;
NullAway is the operating nullness gate and runs as a **blocking** CI job
(`nullaway` in `code_quality.yml`). The EISOP NullnessChecker stays opt-in per
module (`-DENABLE_NULLNESS`) for local conformance runs but is not a CI gate —
its full-checker compile hangs ~6h on GitHub Actions (the `checkerFramework`
job is disabled with `if: false`). The per-module/per-wave commit history is in
the PR description.

**ℹ️ Rebased on `main` (`624adc3699`).** The branch was replayed onto the
current `main` (55 commits past the previous base `76167728c6`): all 75 commits
linear, conflicts resolved with **main's API priority** (JMLtk 1.0.1 generic
meta-construct grammar `#4025` — `@TransformerMeta` registry, `KeyMetaConstruct`
node, transformer renames; PMap LDTs `#4024`; `metaDisjoint` fix `#4031`;
`GenerationalCache` OSS/MT refactor `#4023`; sequence strategies `#4026`;
key.ui window/recent-files fixes `#4027`/`#4028`) with the branch's JSpecify
annotations re-applied. NullAway findings introduced by main's new code were
driven to zero (guards + honest `@Nullable` widenings in `AppliedRuleAppsNameCache`,
`SeqStrategy`, `SeqEqualLengthFeature`, `JP2KeYConverter`, `EnhancedForElimination`,
`TestTacletParser`). Locally verified on the new head: `spotlessCheck`,
`testClasses`, and the full NullAway gate
`./gradlew -DENABLE_NULLAWAY=true compileTestJava` → **0 findings**, all modules.

## Strategy (agreed with maintainer)

1. **Goal 1 — annotations only.** Parallel annotation campaign across disjoint
   package clusters. Verified by `javac` compile (fast: 40 s baseline) +
   spotless. ✅ done — all modules annotated.
2. **Goal 2 — fast trials.** **NullAway** (Uber) as an opt-in, incremental,
   JSpecify-aware checker (`-DENABLE_NULLAWAY`) to validate the annotations
   quickly while iterating. ✅ done — and it became the operating CI gate:
   `./gradlew -DENABLE_NULLAWAY=true compileTestJava` runs as the blocking
   `nullaway` job and reports 0 findings across every module.
3. **Goal 3 — EISOP semantics.** The **EISOP NullnessChecker** was driven clean
   per module during the campaign; its wiring stays opt-in via
   `-DENABLE_NULLNESS`. As the *CI* gate it was dropped (hangs ~6h on
   GitHub Actions) — NullAway is the operating gate.

## Module scope & dependency order

```
key.util (78)                  ✅ DONE — annotated, EISOP-checked
  → key.ncore (46)             ✅ DONE — annotated, EISOP-checked
    → key.ncore.calculus (127) ✅ DONE — annotated, EISOP-checked
      → key.ncore.matcher (29) ✅ DONE — annotated, EISOP-checked
        → key.core (1573)      ✅ DONE — 10 package clusters (waves 1–3)
          → Level 1 (depend only on key.core):  ✅ DONE — key.core.wd (16),
            key.core.testgen (41), key.core.infflow (98), key.core.example (1)
          → Level 2: ✅ DONE — keyext.slicing (37), keyext.exploration (13),
            key.ui (372; also depends on infflow+wd+all keyext)
          → Level 3: ✅ DONE — keyext.caching (19), keyext.isabelletranslation (42),
            keyext.proofmanagement (26), keyext.ui.testgen (7)
```

Execution order: dependency chain first; within a level, bigger modules first.
Every module was processed package-by-package; each module was driven
NullAway-clean (main + test sources) before the next one started.

## Final state

- All modules carry JSpecify `@NullMarked` scopes and precise `@Nullable`
  type-use annotations (arrays, nested types, generic bounds). Behavior is
  unchanged: only honest `@Nullable` widenings, crash-equivalent
  `Objects.requireNonNull` guards at pre-existing crash points, and scoped
  justified `@SuppressWarnings("NullAway")`.
- `./gradlew -DENABLE_NULLAWAY=true compileTestJava` → 0 findings (all modules:
  main + test + testFixtures).
- `./gradlew spotlessCheck` → green.
- CI (`code_quality.yml`): `nullaway` job **blocking** (ran with
  `continue-on-error` until the campaign finished); `checkerFramework` job
  disabled (`if: false`, EISOP hangs on CI).
- Build/config: Gradle 9.8, JDK 25 toolchain (release 21), clean build compiles
  in ~40 s. Spotless Eclipse formatter + importOrder(`java|javax`, `de.uka`,
  `org.key_project`, `''`, `\#`) + license headers + `removeUnusedImports`.
  JSpecify 1.0.1 via `compileOnly(libs.jspecify)` in `gradle/libs.versions.toml`.

## Annotation conventions (from the jspecify-nullness skill)

- Imports from `org.jspecify.annotations`: `NullMarked`, `Nullable`, `NonNull`,
  `NullUnmarked`.
- **Class-level `@NullMarked`** on every class/interface/enum in the cluster
  (matches existing key.core style); `@Nullable` only where null is genuinely
  allowed (matching `return null`, `== null` guards, nullable fields, null
  passed at call sites).
- Do **not** annotate local-variable root types or cast roots; only type args /
  array components inside them.
- Arrays: `@Nullable String[]` (nullable elements) vs `String @Nullable []`
  (nullable array ref); same nesting rules for `.@Nullable` nested types.
- Generics: annotate a type-variable use only when its nullness differs from the
  type argument; add `T extends @Nullable Object` bounds only when nullable type
  args must be supported. Do not write `<@Nullable T>`.
- `@NullUnmarked` only as an escape hatch for legacy pockets; report them.
- Never change method behavior, only annotations and imports (crash-equivalent
  guards and scoped, justified suppressions are the only allowed exceptions).
- Every file keeps: license header, javadoc, existing `@formatter:on/off`
  blocks, and the spotless import order.

## key.core clusters (waves 1–3)

| # | Cluster | Paths (relative `key.core/src/main/java/de/uka/ilkd/key/`) | Files |
|---|---------|-------------------------------------------------------------|-------|
| 1 | logic | `logic/**` (incl. op, label, sort, equality, util) | ~113 |
| 2 | java/ast | `java/ast/**` | ~203 |
| 3 | rule | `rule/**` (incl. metaconstruct, conditions, match, merge, tacletbuilder, label, inst, executor) | ~257 |
| 4 | java/other | `java/**` (top level), `java/transformations`, `java/visitor`, `java/loader` | ~74 |
| 5 | proof | `proof/**` (incl. io, init, mgt, join, delayedcut, calculus, replay, reference, event, proofevent, rules) | ~179 |
| 6 | strategy | `strategy/**` (incl. feature, quantifierHeuristics, termProjection, termgenerator, termfeature, definition) | ~196 |
| 7 | speclang | `speclang/**` (incl. jml, njml, infflow, translation, dl) | ~101 |
| 8 | smt | `smt/**` (incl. newsmt2, lang, communication, model, solvertypes, hierarchy) | ~104 |
| 9 | pp+util+scripts+macros | `pp/**`, `util/**`, `scripts/**` (incl. meta), `macros/**` | ~187 |
| 10 | misc | `ldt`, `nparser/**`, `parser`, `prover/**`, `control/**`, `axiom_abstraction/**`, `taclettranslation/**`, `settings/**` | ~152 |

Waves (dependency-aware, each validated by compile + spotless before the next):
- Wave 1: clusters 1, 2, 3 — foundational (terms, AST, rules).
- Wave 2: clusters 4, 5, 6 — java plumbing, proof, strategy.
- Wave 3: clusters 7, 8, 9, 10 — speclang, smt, utilities, remaining.

## Phase 2 — NullAway fast trials (done; now the CI gate)

Dependencies (version catalog): `com.uber.nullaway:nullaway:0.14.3`,
`com.google.errorprone:error_prone_core:2.49.0`, and the Gradle plugins
`net.ltgt.errorprone` 5.1.1 + `net.ltgt.nullaway` 3.3.0.

Why the plugin route: NullAway 0.14.x is an Error Prone `BugChecker` — it ships
no `com.sun.source.util.Plugin` service, so `-Xplugin:NullAway` cannot load it
(trial confirmed: "plug-in not found"). It must run inside Error Prone.

Wiring (in `build.gradle`, opt-in via `-DENABLE_NULLAWAY`, off by default):
- root `plugins {}`: `alias(libs.plugins.errorprone) apply false`,
  `alias(libs.plugins.nullaway) apply false`
- subprojects: `apply plugin: "net.ltgt.errorprone"` + `"net.ltgt.nullaway"`;
  dependencies: `errorprone(libs.errorprone.core)` + `errorprone(libs.nullaway)`
- per `JavaCompile`:
  ```
  options.errorprone.enabled = false
  if (System.getProperty("ENABLE_NULLAWAY")) {
      options.errorprone.enabled = true
      options.errorprone.disableAllChecks = true
      options.errorprone.nullaway.severity.set(
          net.ltgt.gradle.errorprone.CheckSeverity.ERROR)
      options.errorprone.nullaway.annotatedPackages.addAll(
          ["de.uka.ilkd.key", "org.key_project"])
      options.errorprone.nullaway.jspecifyMode.set(true)
  }
  ```
  (`options.errorprone.nullaway` exists because the nullaway plugin registers a
  `NullAwayOptions` extension named "nullaway" *on the ErrorProne options*;
  ERROR severity turns the gate into "build fails until findings are zero";
  `-Xmaxerrs 10000` lifts javac's default 100-error cap so one pass reports the
  full finding set.)
- Gate run: `./gradlew -DENABLE_NULLAWAY=true compileTestJava` (compiles main +
  test + testFixtures of every module; stops at the first failing module).

**Result:** findings were driven to zero across all modules with a fixed
priority — honest `@Nullable` widening → crash-equivalent
`Objects.requireNonNull` at pre-existing crash points → scoped
`@SuppressWarnings("NullAway")` with a justification. The gate was then flipped
from `continue-on-error` to a **blocking** CI job (`nullaway` in
`code_quality.yml`).

## Phase 3 — EISOP conformance (per module; not a CI gate)

- The EISOP NullnessChecker was enabled per module behind `-DENABLE_NULLNESS`
  (with `-AonlyDefs` scoping + `-Werror`) and driven clean during the campaign
  (per-module fix history in the PR description).
- As the CI gate it was dropped: a full-checker compile hangs ~6h on GitHub
  Actions, so the `checkerFramework` job in `code_quality.yml` is disabled
  (`if: false`). NullAway is the operating CI gate.
- The per-module EISOP wiring remains opt-in for local conformance runs; flip
  `if: false` → `if: true` in `code_quality.yml` to restore the CI run.

## Out of scope

- The stale `eisop/keycore2` branch (3013 commits behind main) — start fresh.
