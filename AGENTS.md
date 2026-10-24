# Agent Instructions

KeY — deductive Java program verifier for the Java Modeling Language.
Using Java 21 and a Gradle multi-module build.

## Core Commands
Use the Gradle wrapper or `gradle` if available. 

| Task | Command |
|------|---------|
| Compile all classes | `./gradlew testClasses` |
| Run GUI | `./gradlew key.ui:run` |
| Full test suite | `./gradlew test` |
| Format file(s) | `./gradlew spotlessApply` |
| Format check | `./gradlew spotlessCheck` |
| Nullness check | `./gradlew -DENABLE_NULLNESS=true compileTestJava` |


## Project Layout
- `key.*` — modules are central
- `keyext.*` — optional extensions, never add them add compile dependency in a central module
- Legacy code lives in `de.uka.ilkd.key.*`; new code should use `org.key_project.*` where possible
- Modules should have distinct packages
- KeY write settings in `$HOME/.key`

## Key Conventions
- Spotless enforce: file header, import order and code formatting. 
- Test are written in JUnit 5 (Jupiter) tests, AssertJ assertions allowed; avoid tags `owntest`, `interactive`, `performance` in normal suites
- Prover tests assume the single-threaded prover (`key.prover.parallel=false`); multi-threaded gates live in `testMt*` Gradle tasks
- Install SMT z3 or cvc5 to run all tests

## Docs & Conventions
- Developer docs & code conventions: https://keyproject.github.io/key-docs/devel/CodingConventions/
- Contribution/licensing process: `CONTRIBUTING.md` (GPLv2-or-later)
- PRs are gated: unit tests, `spotlessCheck`, Checker Framework nullness build
- Use the template: `.github/pull_request_template.md` when you file a PR. Avoid unecessary line breaks in PR description. 
- Branch should be linear, i.e. free of merges.
- `script/format_branch_with_spotless.sh` allows you to reformat a series of commits
- Avoid single spotless commits. The whole branch instead. 
- Commit regulary, only push and open PR if the user requests. 
- NEVER ever push on main. 
- Document on public classes, and public methods. Documentation on private methods is optional. 
  Avoid long comments, try to produce readable code. 
- Use slf4j, and LOGGER constants. Do not write on sysout/syserr. 


## Commit Attribution
AI commits MUST include:
```
Co-Authored-By: (the agent model's name and attribution byline)
```
Example: `Co-Authored-By: OpenCode 2.1`
