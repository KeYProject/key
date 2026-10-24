# Agent Instructions

KeY — deductive Java program verifier (JML). Java 21, Gradle multi-module build.

## Core Commands
Use the Gradle wrapper; never call `gradle` directly.
| Task | Command |
|------|---------|
| Compile (incl. JavaCC/ANTLR) | `./gradlew classes` |
| Run GUI | `./gradlew key.ui:run` |
| Fast test suite (minutes) | `./gradlew testFast` |
| Full test suite (hours) | `./gradlew test` |

## File-Scoped Commands
Tests run per module; `--tests` accepts wildcards (`".*"`, `"Class.method"`).
| Task | Command |
|------|---------|
| Single test | `./gradlew :key.core:test --tests "de.uka.ilkd.key.util.TestName.method"` |
| Test class | `./gradlew :keyext.slicing:test --tests "de.uka.ilkd.key.slicing.*"` |
| Format file(s) | `./gradlew :<module>:spotlessApply` |
| Format check | `./gradlew spotlessCheck` |
| Nullness check | `./gradlew -DENABLE_NULLNESS=true compileTestJava` |

## Project Layout
- `key.util`, `key.core`, `key.ui` — the KeY prover product; changes here need special care
- `key.ncore`, `key.ncore.calculus`, `key.ncore.matcher` — new core (`org.key_project.*` packages)
- `keyext.*` (proofmanagement, exploration, slicing, testgen, ...) — optional extensions
- Legacy code lives in `de.uka.ilkd.key.*`; new code should use `org.key_project.*` where possible
- Structured formats: `.key` (taclets), `.proof`, `.script`, `.jml` — do not hand-edit unless needed

## Key Conventions
- Every Java file needs the GPLv2 license header (Spotless-enforced):
```java
/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2,
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
```
- Import order (Spotless-enforced): `java|javax`, `de.uka`, `org.key_project`, `<empty>`, static
- Java 21 source/target; formatting from `scripts/tools/checkstyle/keyCodeStyle.xml`
- JUnit 5 (Jupiter) tests, AssertJ assertions; avoid tags `owntest`, `interactive`, `performance` in normal suites
- Prover tests assume the single-threaded prover (`key.prover.parallel=false`); multi-threaded gates live in `testMt*` Gradle tasks
- SMT solver tests need Z3/cvc5 on `PATH` (CI pins Z3 4.13.0)

## Docs & Conventions
- Developer docs & code conventions: https://keyproject.github.io/key-docs/devel/ (see `CodingConventions`)
- Contribution/licensing process: `CONTRIBUTING.md` (GPLv2-or-later)
- PRs are gated: tests, `spotlessCheck`, Checker Framework nullness build

## Commit Attribution
AI commits MUST include:
```
Co-Authored-By: (the agent model's name and attribution byline)
```
Example: `Co-Authored-By: Claude Sonnet 4 <noreply@example.com>`
