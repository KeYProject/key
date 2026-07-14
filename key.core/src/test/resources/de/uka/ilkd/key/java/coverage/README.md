# Java feature coverage examples

Fixtures for `de.uka.ilkd.key.java.JavaFeatureCoverageTest`, which pins down
which Java language features KeY's front-end currently parses. They also back
the **Java Coverage** support table in the user documentation
(*User Guide > Supported Language Features > Java Coverage*).

Layout: one directory per feature, each with a small `.java` file plus a
`problem.key` (`\javaSource "."; \problem { true }`) that makes KeY parse it:

- `supported/`: features KeY **parses** today. The test loads each and fails
  if one stops parsing (a front-end regression).
- `rejected/`: features KeY does **not** parse today (loading throws, usually
  *"Unsupported element detected given by Java Parser"*). The test fails if one
  starts parsing, which means the feature became supported and both the test
  and the documentation table must be updated.

Every `.java` file also compiles with `javac` 21, and uses only types available
in KeY's default classpath (`JavaRedux`) or types it declares itself, so a load
failure reflects KeY's front-end and not malformed Java or a missing type.

## Why each rejected example is rejected

Each example isolates a single construct, so its rejection is attributable to
the feature under test (verified by loading each and inspecting the error):

| Example | Rejected because |
|---|---|
| `generics-*` (plain, bounded, wildcard, method, diamond) | converter aborts with *"Unexpected type to convert"* on the type parameter/argument |
| `local-class` | `Unsupported element: LocalClassDeclarationStmt` |
| `static-import` | `Unsupported element: ImportDeclaration` (the `static` import) |
| `annotation-declaration` | `Unsupported element: AnnotationDeclaration` (the `@interface`) |
| `lambda` | `Unsupported element: LambdaExpr` |
| `method-reference` | `Unsupported element: MethodReferenceExpr` |
| `instanceof-pattern` | `Unsupported element: TypePatternExpr` (the bound pattern) |
| `switch-expression` | parser rejects `yield` / arrow-switch (syntax error) |
| `switch-pattern-type` | `Unsupported element: TypePatternExpr` (`case Integer i`) |
| `switch-pattern-record` | `Unsupported element: TypePatternExpr` (record component of `case Point(...)`) |
| `record-pattern` | `Unsupported element: TypePatternExpr` (record pattern via `instanceof`) |
| `switch-enum-unqualified` | KeY cannot resolve the **unqualified** `case RED` label (the enum is declared in the file, so this is the label form, not a missing type) |
| `module-declaration` | `module-info` currently triggers an internal error (`IndexOutOfBoundsException`) |
| `var-reference-type` | a `var` with a `String` initializer currently triggers an internal `NullPointerException` |

Because the host construct is otherwise supported (a `switch` statement,
`instanceof`, a normal class), the failure lands on the tested feature, not on
its surroundings.

## Notes

- `switch-enum-qualified` vs `switch-enum-unqualified` capture a real quirk: a
  `switch` over an `enum` only loads with *qualified* case labels
  (`case E.C:`); the standard unqualified `case C:` fails to resolve.
- Pattern matching for `switch` is split by pattern kind:
  `switch-pattern-type` and `switch-pattern-record` are rejected, but a bare
  `case null` label (`switch-null-label`) actually parses, so it lives in
  `supported/`. The examples use `switch` *statements*, not `switch`
  *expressions*, so the failure is attributed to the pattern and not to the
  (also unsupported) switch-expression form.
- `var-primitive` / `var-in-for` load, but `var-reference-type` does not.
- Generics come in five variants (`plain`, `bounded`, `wildcard`, `method`,
  `diamond`), all rejected.
- "Parses" is not "soundly reasoned about": `autoboxing` and
  `try-with-resources` sit in `supported/` because they load, but KeY does not
  model them soundly (see the documentation's *Comments* column).
