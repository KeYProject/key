# GitHub Code Coverage Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce one aggregated JaCoCo coverage report in GitHub Actions and upload it as Cobertura XML to GitHub Code Quality.

**Architecture:** The existing opt-in JaCoCo setup gains an aggregated root report and a Cobertura conversion task. GitHub Actions reuses the Ubuntu unit-test legs for execution data, then a small coverage job compiles, aggregates, converts and uploads.

**Tech Stack:** Gradle 9.8.2, JaCoCo 0.8.16, Python 3 (`jacoco2cobertura.py`), GitHub Actions (`actions/upload-code-coverage@v1`).

**Spec:** `docs/superpowers/specs/2026-11-24-github-code-coverage-design.md`

## Global Constraints

- JaCoCo tool version: `0.8.16`.
- Aggregated JaCoCo XML: `build/reports/jacoco/root/jacocoRootReport.xml`.
- Cobertura XML: `build/reports/jacoco/root/cobertura.xml`.
- Upload label: `code-coverage/jacoco`, language `Java`, `fail-on-error: false`.
- Existing GitLab/SonarQube invocation must keep working: `-DjacocoEnabled=true testFast sonarqube`.
- Coverage runs only on `ubuntu-24.04`; `windows-latest` legs stay coverage-free.
- Do not add a third-party Gradle plugin.

## Review Focus

- Class files with `$` in the name (inner/local/anonymous classes): the converter must not emit a filename that does not resolve, or GitHub will drop those classes.
- Modules whose package path exists in more than one module source root: filenames must resolve against the correct root.
- Missing execution data (a leg failed before running tests): the report task must not fail the whole coverage job for an absent `*.exec`.
- Upload failure or disabled Code Quality: the job exits successfully with an annotation.
- Windows leg accidentally enabling JaCoCo: runtime and artifact noise must stay off Windows.

---

### Task 1: Build support for aggregated coverage and Cobertura output

**Files:**
- Modify: `scripts/jacocokey.gradle`
- Create: `scripts/tools/jacoco2cobertura.py`

**Interfaces:**
- Consumes: nothing.
- Produces: Gradle tasks `jacocoRootReport` (XML at `build/reports/jacoco/root/jacocoRootReport.xml`) and `jacocoCobertura` (Cobertura at `build/reports/jacoco/root/cobertura.xml`), both available only with `-DjacocoEnabled=true`.

- [ ] **Step 1: Add the converter**

Create `scripts/tools/jacoco2cobertura.py` invoked as
`jacoco2cobertura.py JACOCO_XML COBERTURA_XML [SOURCE_ROOT ...]`. It emits one
Cobertura `<class>` per JaCoCo `<sourcefile>` with the repository-relative path
resolved from the source roots, `hits` = 1 when JaCoCo's `ci` > 0, and skips
source files no source root contains (generated sources). It prints a one-line
summary of packages, files, skipped files and covered/total lines to stderr.

- [ ] **Step 2: Bump JaCoCo and add the root tasks**

In `scripts/jacocokey.gradle`:

1. Set `toolVersion = '0.8.16'`.
2. Keep the `subprojects` block unchanged.
3. Register `jacocoRootReport` of type `JacocoReport` with group `verification`:
   - `executionData.from(fileTree(rootProject.rootDir) { include '*/build/jacoco/*.exec' })`;
   - for every subproject with the `java` plugin: `dependsOn` its `classes` task, add `sourceSets.main.java.srcDirs` to `sourceDirectories`, add `sourceSets.main.output.classesDirs` to `classDirectories`;
   - report only XML, output location `build/reports/jacoco/root/jacocoRootReport.xml`.
4. Register `jacocoCobertura` of type `Exec`, group `verification`, `dependsOn 'jacocoRootReport'`:
   - `commandLine` is `python3`, the absolute path of `scripts/tools/jacoco2cobertura.py`, the absolute path of the aggregated XML, the absolute path of the Cobertura file, followed by each subproject's committed `src/main/java` directory relative to the root project (deduplicated);
   - declare the XML as input and the Cobertura file as output.

- [ ] **Step 3: Generate a real report locally**

Run: `./gradlew -DjacocoEnabled=true :key.ncore:test jacocoRootReport jacocoCobertura`
Expected: `BUILD SUCCESSFUL`; both XML files exist.

- [ ] **Step 4: Validate the Cobertura report**

Run:

```bash
python3 - <<'PY'
import xml.etree.ElementTree as ET, os
root = ET.parse('build/reports/jacoco/root/cobertura.xml').getroot()
sources = [s.text for s in root.find('sources')]
classes = root.findall('.//class')
assert classes, 'no classes'
assert 0.0 <= float(root.attrib['line-rate']) <= 1.0
missing = [c.attrib['filename'] for c in classes
           if not any(os.path.exists(os.path.join(s, c.attrib['filename'])) for s in sources)]
assert len(missing) < len(classes) * 0.05, missing[:10]
assert any(line.findall('line') for line in root.findall('.//class'))
print(f'classes={len(classes)} unresolved={len(missing)} line-rate={root.attrib["line-rate"]}')
PY
```

Expected: prints class count, `unresolved=0` (emitted filenames must all exist), and a line rate between 0 and 1.

- [ ] **Step 5: Commit**

```bash
git add scripts/jacocokey.gradle scripts/tools/jacoco2cobertura.py
git commit -m "build: aggregate JaCoCo coverage and convert it to Cobertura"
```

---

### Task 2: Upload coverage from the GitHub Actions test workflow

**Files:**
- Modify: `.github/workflows/tests.yml`

**Interfaces:**
- Consumes: `jacocoRootReport` and `jacocoCobertura` from Task 1.
- Produces: artifacts `jacoco-core` and `jacoco-rest`; job `coverage` uploading `build/reports/jacoco/root/cobertura.xml`.

- [ ] **Step 1: Enable coverage in the Ubuntu unit-test legs**

In the `unit-tests` job, make the Gradle invocation append `-DjacocoEnabled=true` only when `matrix.os == 'ubuntu-24.04'`, and add a step after the test run that uploads `**/build/jacoco/*.exec` as `jacoco-${{ matrix.group }}` with `if: matrix.os == 'ubuntu-24.04'` and `if-no-files-found: error`. Keep the existing test-result upload unchanged.

- [ ] **Step 2: Add the coverage job**

Add a `coverage` job that:
- `needs: unit-tests`, `if: github.event_name != 'merge_group'`, `runs-on: ubuntu-24.04`, `timeout-minutes: 30`;
- declares job permissions `contents: read`, `code-quality: write`, `pull-requests: read`;
- checks out, sets up JDK 21 (Corretto) and Gradle, then downloads all `jacoco-*` artifacts with `merge-multiple: true`;
- runs `./gradlew -DjacocoEnabled=true jacocoRootReport jacocoCobertura`;
- uploads with `actions/upload-code-coverage@v1`, input `file: build/reports/jacoco/root/cobertura.xml`, `language: Java`, `label: code-coverage/jacoco`, `fail-on-error: false`.

- [ ] **Step 3: Check the workflow parses**

Run: `python3 -c "import yaml,sys; yaml.safe_load(open('.github/workflows/tests.yml')); print('ok')"`
Expected: `ok`.

- [ ] **Step 4: Commit**

```bash
git add .github/workflows/tests.yml
git commit -m "ci: upload JaCoCo coverage to GitHub code coverage"
```

---

### Task 3: Branch-level verification and pull request

**Files:**
- Modify: `docs/superpowers/specs/2026-11-24-github-code-coverage-design.md` (only if verification changes a decision)

**Interfaces:**
- Consumes: all previous tasks.
- Produces: pushed branch and pull request.

- [ ] **Step 1: Run formatting and build-tool checks**

Run: `./gradlew spotlessCheck` and `./gradlew -DjacocoEnabled=true testClasses`
Expected: both succeed.

- [ ] **Step 2: Re-run the report end to end**

Run: `./gradlew -DjacocoEnabled=true jacocoRootReport jacocoCobertura`
Expected: `BUILD SUCCESSFUL`; `build/reports/jacoco/root/cobertura.xml` contains `line-rate` and `<line>` elements.

- [ ] **Step 3: Push and open the pull request**

Push with `git push -u origin ci/github-code-coverage`. Create the PR against `main` using `.github/pull_request_template.md`, with a summary of the build, workflow and manual Code Quality prerequisite, and the verification commands that were run.
