# Compiler Warning Cleanup Plan

Goal: drive the `-Xlint:all` warning count (baseline: **619 warnings, 214 files,
13 categories, 15 modules**, see `docs/warnings.md`) to zero — or to a small,
justified residue of `@SuppressWarnings` — without changing behavior.

## Ground rules (binding for all workstreams)

1. **Behavior preservation is the prime directive.** Every change must be a
   pure warnings-cleanup. When the "obvious" fix risks any behavioral change,
   add `@SuppressWarnings("<category>")` at the narrowest possible scope (with
   a one-line comment) instead.
2. Never change logic, API signatures, semantics, or test assertions.
3. Only touch files owned by your workstream (list in
   `build/warnings/ws-<name>.txt`).
4. Run `spotlessApply` (`./gradlew spotlessApply` for touched modules) and
   compile the touched modules (`./gradlew :key.<module>:compileJava ...
   :compileTestJava --offline`) before committing.
5. Commit per category (or per small file group) with clear messages and the
   AI attribution trailer:
   `Co-Authored-By: OpenCode (KIT Medium)`.
   Never push. Keep the branch linear.
6. If a warning cannot be cleanly resolved, suppress it (see below) and note
   it in the report. Do not delete code to silence warnings.

## Workstreams (disjoint file ownership)

| WS | File count | Warnings | Focus |
|---|---|---|---|
| serial | 80 | 239 (190 serial + 32 this-escape + 8 deprecation + misc) | `serialVersionUID`, plus everything else in those UI/extension files |
| deprecation-main | 31 | 134 | `deprecation` in `src/main` of key.core, key.ncore, key.util, ... |
| deprecation-test | 17 | 97 | `deprecation` in tests/fixtures |
| this-escape | 30 | 53 | constructor `this` escapes |
| unchecked-rawtypes | 35 | 63 | `unchecked` + `rawtypes` |
| misc | 21 | 33 | auxiliaryclass, cast, dangling-doc-comments, try, static, overrides, text-blocks, varargs |

## Category strategy

- **serial**: add `private static final long serialVersionUID = 1L;` to each
  `Serializable` class lacking one (javac's recommended default). Suppress only
  if a fixed UID is genuinely undesirable (rare).
- **this-escape**: if `this` is published before the constructor finishes
  (initialize/listener/thread calls), prefer minimal, provably
  behavior-preserving refactors; otherwise `@SuppressWarnings("this-escape")`
  with a comment. Never defer real work to avoid this lint if the class is
  part of the prover core (Proof, Taclet, ...) — there, suppress with
  justification for a dedicated follow-up.
- **deprecation**: migrate to the non-deprecated successor when the successor
  is evident and used elsewhere in the codebase; otherwise
  `@SuppressWarnings("deprecation")` (tests often intentionally exercise the
  deprecated API).
- **unchecked / rawtypes**: prefer `@SuppressWarnings("unchecked")` /
  `"rawtypes"` at method scope over risky casts; add type arguments only when
  trivially correct.
- **cast**: remove redundant casts. **static**: use the class name.
  **overrides**: add `@Override`. **dangling-doc-comments**: attach/move the
  comment onto the declaration.
- **try**: fix or suppress per instance (empty try-with-resources etc.).
- **auxiliaryclass / text-blocks / varargs**: inspect each; suppress with a
  comment when the fix is not clearly beneficial (text-blocks: prefer
  suppress; use a text block only if byte-identical).

## Integration (coordinator, after all workstreams report)

1. Cherry-pick each workstream's commits onto `weigl/cleanwarnings`
   (keeps history linear).
2. Full verification: `./gradlew testClasses spotlessCheck` (offline),
   plus the warning-specific tests if cheap.
3. Regenerate `build/warnings/warnings.md`; if counts dropped, refresh
   `docs/warnings.md` and commit.
4. Report residual warnings (the suppressed-only residue).
