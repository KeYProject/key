# KeY compiler warning inventory

* generated: 2026-10-25T22:35:00+00:00
* command: `./gradlew --console=plain testClasses --offline --rerun-tasks`

Total warnings: **0** across **0** modules, in **0** categories.

## Summary by category

| category | count |
|---|---|
| _(none — clean)_ | 0 |

## Summary by module

| module | count |
|---|---|
| _(none — clean)_ | 0 |

## Details (grouped by category, module, file)

The full `testClasses` build (all main and test sources of every module, compiled
with `-Xlint:all,-serial,-this-escape` in the shared `JavaCompile` configuration,
reporting cap raised via `-Xmaxwarns 100000`) produces **no javac lint warnings**
and **no javadoc-lint diagnostics** on the classic `/** */` files. The remaining
80 javadoc diagnostics are the accepted markdown `///` doc-comment residue, see
[`docs/javadoc.md`](javadoc.md) and [`docs/javadoc-plan.md`](javadoc-plan.md).
