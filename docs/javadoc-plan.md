# Javadoc Diagnostics Cleanup Plan

Goal: drive `./gradlew javadoc` diagnostics from the baseline to **zero**
(excluding the accepted residue from markdown `///` doc comments, see "Out of
scope") without touching code behavior. This is the javadoc counterpart of the
javac lint cleanup (`docs/warnings-plan.md`).

## Baseline

First measurement (2026-10-25, `./gradlew --console=plain javadoc --offline`,
after raising the javadoc reporting caps):

- **0 errors, ~196 reported warnings → 124 unique diagnostics** (javadoc
  repeats many messages; uniqueness is by `file:line:message`).
- 104 unique warnings are **located** in ~30 files; ~58 raw (20 unique) are
  reported **without a location** and all stem from markdown `///` doc
  comments (see "Out of scope").
- **In scope: ~97 unique diagnostics** across ~22 files with classic
  `/** ... */` javadoc comments (modules: key.core, key.ncore, key.ui,
  key.util). The rest (~27 unique) are **accepted residue** in markdown
  `///` comments that are intentionally not rewritten.

### Reproducing the inventory

- `build.gradle` already raises the caps (`tasks.withType(Javadoc).configureEach`):
  `-Xmaxerrs 10000` and `-Xmaxwarns 10000` (javadoc caps each at 100 by default,
  which silently truncated the list).
- `scripts/collect-javadoc.py` runs the build, parses `path:line: (error|warning): msg`
  (keeping unlocated warnings under `(no location)`), and writes the grouped
  report to `build/warnings/javadoc.md`. Full log: `build/warnings/javadoc.log`.
- Usage: `python3 scripts/collect-javadoc.py [gradle args...]` (or `--no-build`
  to re-parse the last log).

## Ground rules (binding for all workstreams)

1. **Doc comments only.** Never change code, signatures, semantics, or tests.
   If a stale comment documents behavior that no longer matches the code,
   adjust the *comment*, not the code.
2. **Markdown `///` doc comments are never rewritten** (Kotlin/Dokka-style
   comments, processed by javadoc as JEP-467 markdown doc comments). Their
   diagnostics are accepted residue — do not "fix" them by converting to
   `/** ... */`, changing `[X]`, or reflowing `@see`. (The codebase already
   tolerates this style, e.g. the existing `@SuppressWarnings("JavadocReference")`
   around `///` docs in `KeYGuiExtension`.)
3. When a classic `/** ... */` link target is gone, prefer pointing to the
   current replacement type **only if it is unambiguous**. Otherwise use
   `{@code TypeName}` or plain prose — do not leave a dead `{@link}`.
4. Links that javadoc cannot resolve need either a resolvable target (import +
   simple name, or FQN of an existing type) or `{@code ...}`/plain text.
5. Run `./gradlew spotlessApply` (touched modules) and re-run
   `python3 scripts/collect-javadoc.py --offline` before committing; a
   workstream is done when its files contribute 0 diagnostics.
6. Commit per workstream (or per small file group) with a clear message and the
   attribution trailer `Co-Authored-By: OpenCode (KIT Medium)`. Never push.
   Keep the branch linear.

## Status (2026-10-25)

All five workstreams are complete. Final full-inventory run
(`python3 scripts/collect-javadoc.py --offline`): **0 errors, 80 warnings** —
every remaining warning is accepted markdown-`///` residue (see Out of scope):
58 unlocated + `Properties.java` 12 + `HasMetaSpaceKey` 4 +
`AbstractBlockContractRule` 3 + `KeYGuiExtension` 2 + `Documentation` 1. All
classic `/** ... */` files contribute 0 diagnostics. `docs/javadoc.md` holds the
refreshed inventory; the collector now excludes javac lint noise and forces a
complete re-run (`--rerun-tasks`) so the inventory is reproducible.

## Workstreams (disjoint file ownership)

| WS | unique diag (approx) | files | focus |
|---|---|---|---|
| ws-javapackage | 63 | 2 | rewrite `key.java/package-info.java` (62 dead recoder-era links); fix `@date` unknown tag in `key.util` `testcategories/package-info.java` |
| ws-java-ast | 8 | 1 | `KeYJavaASTFactory.java`: links to removed operator types (`LogicalAnd`, `LogicalOr`, `Equals`, `LessThan`, `NotEquals`) |
| ws-dead-links | 15 | 7 | `{@link}` targets in classic comments that no longer exist (see strategy) |
| ws-links-unresolvable | 2 | 1 | classic-comment links resolving to inaccessible/non-matching members (`#CAP`) |
| ws-tags | 16 | 11 | HTML escape, tag syntax typos, unknown tags, stale `@param`/`@throws` (see strategy) |

## Diagnostics and strategies

### ws-javapackage — `key.java/package-info.java` (62)

The package overview documents the **removed** recoder-based Java model
(`de.uka.ilkd.key.java.{SourceElement, ModelElement, Comment, ProgramElement,
TerminalProgramElement, NonTerminalProgramElement, CompilationUnit,
JavaSourceElement, JavaProgramElement, Recoder2KeY, SchemaRecoder2KeY}`).
None of those types exist anymore (only `KeYJavaASTFactory` remains); the
package now contains `ast/` (203 files), `transformations/`, `visitor/`,
`loader/`, and a few top-level classes. This file is a classic `/** */` comment.
→ Rewrite the overview to describe the current structure (AST in
`de.uka.ilkd.key.java.ast`, the transformation pipeline, visitors), referencing
only existing types, or drop `{@link}`/use `{@code}`. Also fix
`key.util/.../testcategories/package-info.java:7` (`@date` is not a javadoc
tag → plain text).

### ws-java-ast — `KeYJavaASTFactory.java` (8)

`{@link LogicalAnd}`, `{@link LogicalOr}`, `{@link Equals}`, `{@link LessThan}`,
`{@link NotEquals}` (lines 305, 320, 693, 708, 722, 1092, 1106, 2143): these
operator classes were **deleted** (no matches anywhere). Fix: `{@code ...}`
or prose (`"a comparison for equality"`), keeping the method docs readable.

### ws-dead-links (15) — classic-comment `{@link}` targets that no longer exist

| site | link | fix |
|---|---|---|
| `proof/io/IProofFileParser.java:10` | `de.uka.ilkd.key.nparser.KeYParser` | target gone → `{@code}`/prose, or correct current parser API |
| `rule/SetStatementBuiltInRuleApp.java:17` | `de.uka.ilkd.key.java.statement.SetStatement` | recoder-era type gone → current AST equivalent or `{@code}` |
| `java/ast/abstraction/Member.java:21` | `recoder.abstraction.Constructor` | not resolvable on this module’s javadoc classpath → `{@code}`/prose |
| `rule/match/vm/instructions/MatchGenericSortInstruction.java:21` | `QualifierWrapper` | verify class name/location; else `{@code}` |
| `rule/match/vm/JavaProgramMatchPlanBuilder.java:81–85` | `LeafPlan`, `ListSVPlan`, `StructuralPlan` (×2) | verify current class names (likely `*Plan` → `LeafDMatchPlan`-style); else `{@code}` |
| `strategy/feature/DeleteMergePointRuleFeature.java:26` | `MergePointStatement` | recoder-era type; use current AST declarator type or `{@code}` |

### ws-links-unresolvable (2)

| site | link | fix |
|---|---|---|
| `strategy/.../tiebreak/PolarityOccurrenceTieBreak.java:107,111` | `{@link #CAP}` | `CAP` is private → `{@code #CAP}` |

(Diagnostics in `///` comments with the same shape — `Properties.java`,
`KeYGuiExtension.java` — are out of scope, see below.)

### ws-tags (16)

- **Raw `<` in prose** (HTML parser): `ModifierKind.java:98`
  (`public < protected < package-private < private` → `{@code ...}` or `&lt;`),
  `transformations/pipeline/ConstructorNormalformBuilder.java:40`.
- **Nested link**: `rule/AbstractAuxiliaryContractBuiltInRuleApp.java:35` →
  flatten/`{@code}`.
- **Unknown tags** (convert to plain text): `rule/QueryExpand.java:569`
  (`@note`); `scripts/meta/Option.java:20` (`@Option(...)` inside a ```java
  code fence — javadoc has no markdown support; wrap the example in
  `<pre>{@code ...}</pre>`); `key.ui` `IssueDialog.java:64` (`@implNote` — this
  JDK’s doclet does not register it; either register via the `-tag` option or
  use prose); `settings/InvalidSettingsInputException.java:11` (`@date`).
- **Stale `@param` names**: `proof/Goal.java:703` (`ruleApp`),
  `rule/executor/javadl/FindTacletExecutor.java:172–174` (`tacletApp`, `gt`,
  `currentSequent`), `rule/TacletApp.java:699` (`services`) — align with the
  actual parameter names (the signatures may have changed; drop or rename the
  tags).
- **`@throws <gone FQN>`**: `util/parsing/SyntaxErrorReporter.java:116,130,145`
  (`de.uka.ilkd.key.parser.proofjava.ParseException` no longer exists) → the
  actually-thrown exception type or drop the tag.

## Out of scope (accepted residue)

Per the campaign decision, **markdown (`///`) doc comments are not rewritten**.
The following diagnostics are therefore accepted residue (~27 unique, ~79 raw
lines) and are **not** covered by the acceptance criteria:

- **Unlocated cluster (~20 unique / 58 raw)** — failing `[X]` / `[#member()]`
  references in `///` comments: `MutableState.java` (`[TermBuffer]`),
  `StopCondition.java` (`[#currentTimeMillis()]`), and further clusters in
  key.ncore.calculus, key.core, key.core.infflow and key.util
  (`ChoicePoint`, `MatchConditions`, `RuleApp`, `TacletGoalTemplate`,
  `#hashCode()`, `Map`, `ProofScriptCommand`, `ParametricSortDecl`,
  `ParametricFunctionDecl`, `ParametricFunctionInstance`, `ProofGoal`,
  `ProofSearchInformation`, `DocumentationGenerator`, `AbstractCommand#execute`,
  `StrategySettings`, `#of(T...)`, `fixed`).
  (Locating them is trivial for anyone who wants to revisit: `git grep -n <text>`.)
- `util/properties/Properties.java:12–13` — `/// WEIGL:` note linking
  `PropertyEntry`/`Configuration` (3 unique).
- `key.ncore` `org/key_project/logic/HasMetaSpaceKey.java:9` — `///` link to
  the stale FQN `de.uka.ilkd.key.logic.MetaSpace` (now
  `org.key_project.logic.MetaSpace`) (1 unique).
- `rule/AbstractBlockContractRule.java:124` — `{@link ...]` bracket typo in a
  `///` comment (1 unique).
- `key.ui` `gui/extension/api/KeYGuiExtension.java:304` — `/// @see
  Profile#prepareInitConfig(InitConfig, Object)` (already guarded by
  `@SuppressWarnings("JavadocReference")`) (1 unique).
- `scripts/meta/Documentation.java:45` — `///` file linking `DocumentationGenerator`
  (1 unique).

If a future javadoc switch allows disabling markdown-doc-comment processing
without touching the sources, that would remove the unlocated residue cleanly —
out of scope for now.

## Out of scope / future (doclint)

`-Xdoclint:none` is active (build.gradle), so doc-comment *content* issues
(missing/empty comments, bad tags, invalid HTML beyond the above) are not part
of this baseline. Revisiting doclint (e.g. `-Xdoclint:reference,html`) is a
sensible follow-up once the above is done, but it will surface a *much* larger
inventory and should be a separate effort.

## Acceptance criteria

- `python3 scripts/collect-javadoc.py --offline` → **0 errors, 0 warnings on
  all classic `/** ... */` files**. The markdown-`///` residue enumerated above
  (~27 unique) remains and is excluded.
- `./gradlew spotlessApply` clean for all touched modules.
- No non-comment/non-javadoc-config source changes: `git diff` per commit
  touches only doc comments and `package-info.java`, plus once each
  `build.gradle` (the cap change), `scripts/collect-javadoc.py`,
  `docs/javadoc.md` (inventory) and `docs/javadoc-plan.md` (this plan).
- No `///` doc comment is modified anywhere.
- Branch stays linear; nothing pushed without approval.
