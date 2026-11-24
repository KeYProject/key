# GitHub code coverage design

## Goal

Publish JaCoCo line coverage for KeY on pull requests and on `main` using GitHub's
native Code Quality code coverage, replacing nothing else: GitLab CI/SonarQube keeps
its existing behaviour.

## Current state

- `scripts/jacocokey.gradle` applies JaCoCo only when Gradle runs with
  `-DjacocoEnabled=true`. It reports per-subproject XML only and pins JaCoCo `0.8.8`,
  which predates Java 21 bytecode support.
- `.gitlab-ci.yml` uses the flag for `testFast sonarqube`.
- `.github/workflows/tests.yml` runs the unit tests in a matrix of
  `{ubuntu-24.04, windows-latest} x {core, rest}` without coverage.

## Requirements

1. Produce one aggregated coverage report for the whole repository.
2. Do not duplicate test execution in GitHub Actions.
3. Upload a Cobertura XML report to GitHub with `actions/upload-code-coverage@v1`.
4. A failed upload must not turn pull requests red (`fail-on-error: false`).
5. Keep the GitLab/SonarQube path working unchanged.

## Design

### Gradle

`scripts/jacocokey.gradle`:

- bump `jacoco.toolVersion` to `0.8.16`;
- keep the per-subproject `jacocoTestReport`;
- add `jacocoRootReport` (`JacocoReport`) at the root project that reads every
  `**/build/jacoco/*.exec`, all subproject `main` class directories and all
  subproject Java source roots, and writes
  `build/reports/jacoco/root/jacocoRootReport.xml`;
- add `jacocoCobertura` (`Exec`) that converts that XML to
  `build/reports/jacoco/root/cobertura.xml` with the vendored converter, passing the
  subproject `src/main/java` directories (repository-relative) as source roots.

### Converter

Add `scripts/tools/jacoco2cobertura.py`, a small converter that emits one
Cobertura `<class>` per source file with repository-relative filenames and only
the line data GitHub consumes. The vendored `cover2cover.py` referenced by
GitHub's documentation was tried first and rejected: it prints Python `bytes`
(invalid XML) and repeats every source file's lines once per class, turning this
repository's 21 MB JaCoCo report into 396 MB. Generated sources, which cannot be
matched to repository files, are skipped.

### GitHub Actions

`.github/workflows/tests.yml`:

- in the `unit-tests` job the `ubuntu-24.04` legs run Gradle with
  `-DjacocoEnabled=true`; the `windows-latest` legs do not;
- those Ubuntu legs upload `**/build/jacoco/*.exec` as `jacoco-<group>` artifacts;
- a new `coverage` job (Ubuntu, `needs: unit-tests`, skipped for `merge_group`):
  1. checks out, sets up JDK 21 and Gradle,
  2. downloads the `jacoco-*` artifacts,
  3. runs `./gradlew -DjacocoEnabled=true jacocoRootReport jacocoCobertura`,
  4. uploads `build/reports/jacoco/root/cobertura.xml` with language `Java`,
     label `code-coverage/jacoco`, `fail-on-error: false`;
  - job permissions: `contents: read`, `code-quality: write`,
    `pull-requests: read`.

### Manual prerequisite

Code Quality with code coverage must be enabled for the `KeYProject/key`
repository. Coverage is free for public repositories but still has to be
activated in the repository settings. The first upload to `main` establishes the
baseline that pull requests are compared against.

## Alternatives considered

- A dedicated coverage job running the whole test suite: rejected because it
  duplicates the long KeY test run.
- A third-party JaCoCo-to-Cobertura Gradle plugin: rejected in favour of a
  small in-repository converter.
- Uploading per-leg reports with separate labels: rejected because the report is
  meant to be one repository-wide aggregate.

## Risks and mitigations

- GitHub matches Cobertura `<class filename>` to repository files. This is
  validated locally against a real module report before the workflow relies on
  it; filenames are emitted repository-relative, so no `<source>` resolution is
  needed.
- Pull requests from forks cannot upload coverage; the upload action exits
  gracefully in that case.
- Only Ubuntu legs contribute coverage, so platform-specific Windows code paths
  are not measured.
- A merged pull request reports coverage for the merge commit while GitHub
  attributes it to the pull request head commit; line numbers can shift if `main`
  changed the same files in the meantime.
