# Plan: JSpecify nullness annotations for the KeY project

Applies the `jspecify-nullness` skill to the KeY project. Continues the goal of
PR #3470 ("Nullness Type System for `key.core`"), which failed because the EISOP
Checker Framework NullnessChecker was too slow over the whole module.
**Scope: every module, following the dependency chain and module size. Inside
modules, package by package.**

## Strategy (agreed with maintainer)

1. **Goal 1 — annotations only.** Parallel annotation campaign across disjoint
   package clusters. Verified by `javac` compile (fast: 40 s baseline) + spotless.
2. **Goal 2 — fast trials.** Add **NullAway** (Uber) as an opt-in, incremental,
   JSpecify-aware checker (`-DENABLE_NULLNESS`-style property) to validate the
   annotations quickly while iterating.
3. **Goal 3 — EISOP semantics.** In the end the **EISOP NullnessChecker**
   (already wired for `key.util`, `key.ncore`, `key.ncore.calculus`,
   `key.ncore.matcher`) is the source of truth. Enable it for `key.core` once
   annotations are stable, and fix semantic mismatches.

## Module scope & dependency order

```
key.util (78)                  ✅ DONE — EISOP-checked
  → key.ncore (46)             ✅ DONE — EISOP-checked
    → key.ncore.calculus (127) ✅ DONE — EISOP-checked
      → key.ncore.matcher (29) ✅ DONE — EISOP-checked
        → key.core (1573)      🔶 IN PROGRESS (Wave 1: clusters 1–3 running)
          → Level 1 (depend only on key.core):  key.core.wd (16),
            key.core.testgen (41), key.core.infflow (98), key.core.example (1)
          → Level 2: keyext.slicing (37), keyext.exploration (13),
            key.ui (372; also depends on infflow+wd+all keyext)
          → Level 3: keyext.caching (19), keyext.isabelletranslation (42),
            keyext.proofmanagement (26), keyext.ui.testgen (7)
```

Execution order: dependency chain first; within a level, bigger modules first.
Every module is processed package-by-package (see key.core cluster example
below). After a module's annotations land, it becomes eligible for the
NullAway fast trial (Phase 2), and finally for the EISOP check (Phase 3).

## Current state (HEAD 2f062389d4)

- Checker enabled (opt-in via `-DENABLE_NULLNESS`): `key.util`, `key.ncore`,
  `key.ncore.calculus`, `key.ncore.matcher` — annotated + clean.
- `key.core`: 1573 main source files, ~90 packages, no checker enabled.
  Only ~10 files carry `@NullMarked` (in `java.ast`, `ldt`).
- Build compiles in ~40 s from clean. Gradle 9.8, JDK 25 toolchain (release 21).
- Formatting: Spotless Eclipse formatter + importOrder(`java|javax`, `de.uka`,
  `org.key_project`, `''`, `\#`) + license headers + `removeUnusedImports`.
- Config: `compileOnly(libs.jspecify)` with jspecify 1.0.1 already in
  `gradle/libs.versions.toml`.

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
- Never change method behavior, only annotations and imports.
- Every file keeps: license header, javadoc, existing `@formatter:on/off`
  blocks, and the spotless import order.

## Parallel work packages (disjoint file sets, one agent each)

| # | Cluster | Paths (relative `key.core/src/main/java/de/uka/ilkd/key/`) | Files |
|---|---------|-------------------------------------------------------------|-------|
| 1 | logic | `logic/**` (incl. op, label, sort, equality, util) | ~113 |
| 2 | java/ast | `java/ast/**` | ~203 |
| 3 | rule | `rule/**` (incl. metaconstruct, conditions, match, merge, tacletbuilder, label, inst, executor) | ~257 |
| 4 | java/other | `java/**` (top level), `java/transformations`, `java/visitor`, `java/loader` | ~74 |
| 5 | proof | `proof/**` (incl. io, init, mgt, join, delayedcut, calculus, replay, reference, event, proo fevent, rules) | ~179 |
| 6 | strategy | `strategy/**` (incl. feature, quantifierHeuristics, termProjection, termgenerator, termfeature, definition) | ~196 |
| 7 | speclang | `speclang/**` (incl. jml, njml, infflow, translation, dl) | ~101 |
| 8 | smt | `smt/**` (incl. newsmt2, lang, communication, model, solvertypes, hierarchy) | ~104 |
| 9 | pp+util+scripts+macros | `pp/**`, `util/**`, `scripts/**` (incl. meta), `macros/**` | ~187 |
| 10 | misc | `ldt`, `nparser/**`, `parser`, `prover/**`, `control/**`, `axiom_abstraction/**`, `taclettranslation/**`, `settings/**` | ~152 |

Waves (dependency-aware, each validated by compile + spotless before the next):
- Wave 1: clusters 1, 2, 3 — foundational (terms, AST, rules).
- Wave 2: clusters 4, 5, 6 — java plumbing, proof, strategy.
- Wave 3: clusters 7, 8, 9, 10 — speclang, smt, utilities, remaining.

If Wave 1 pilot looks good, later waves run with more concurrency.

## Execution workflow per wave

1. Dispatch one background subagent per cluster; prompt contains cluster spec,
   skill conventions, report contract. Agents edit **only** their cluster,
   never run Gradle, never commit.
2. On wave completion: `./gradlew spotlessApply :key.core:compileJava` (fast
   validation; catches import/wiring mistakes).
3. Review agent reports; spot-check representative files against the skill.
4. Commit per cluster (`feat(nullness): annotate <cluster> [PR #3470 follow-up]`).
5. Ledger: `.superpowers/sdd/progress.md`.

## Phase 2 — NullAway fast trials (after Wave 1 landed)

Dependency (already added to version catalog): `com.uber.nullaway:nullaway:0.14.3`.

Proposed wiring (apply + test only in the dedicated Phase 2 step, behind a
property so the default build stays untouched):
- In `build.gradle` subprojects block, add `compileOnly(libs.nullaway)` so the
  plugin jar is on the javac classpath, and in
  `tasks.withType(JavaCompile).configureEach`:
  ```
  if (System.getProperty("ENABLE_NULLAWAY")) {
      options.compilerArgs += [
          "-Xplugin:NullAway AnnotatedPackages=de.uka.ilkd.key,org.key_project",
      ]
  }
  ```
  (exact `-Xplugin` argument syntax to be confirmed with a trial run; NullAway
  0.14.x reads JSpecify `@NullMarked`/`@Nullable` from the classpath).
- Trial runs: `./gradlew -DENABLE_NULLAWAY=true :key.core:compileJava`
- Fix findings per package, then keep the property off by default until the
  module is clean; afterwards wire into the CI job alongside EISOP.

## Phase 3 — EISOP conformance (final gate)

- Enable EISOP NullnessChecker for `key.core` behind `-DENABLE_NULLNESS`
  (with `-AonlyDefs` scoping + `-Werror` as in the other modules).
- Fix semantic differences between NullAway and EISOP readings.
- Wire into `code_quality.yml` CI once green.

## Out of scope for now

- `key.core.wd`, `key.core.infflow`, `key.core.testgen`, `key.ui`, `keyext.*`
  (follow same process later).
- The stale `eisop/keycore2` branch (3013 commits behind main) — start fresh.
