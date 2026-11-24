# Switch Expressions and Switch Patterns Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add proof-level support for Java switch expressions (JEP 361) and pattern matching in `switch` (JEP 440/441) to KeY, for both the statement and the expression form.

**Architecture:** New KeY AST nodes (`SwitchExpression`, `Yield`, `PatternCase`) plus a proof-time rewrite in a new **built-in rule**. The rule introduces temporaries (via `EvaluateArgs.evaluate`), replaces each switch expression by its temporary, and emits a plain `Switch` statement, which the existing `#switchToIf` rule lowers. Pattern labels are lowered by the same built-in rule into an `if`-cascade with `instanceof` guards.

**Tech Stack:** Java 21, Gradle wrapper, KeY built-in rules (with the existing `#switchToIf` meta-construct), JUnit 5, jmlparser (fork `Contract-LIB/jmlparser`, published as `io.github.jmltoolkit:jmlparser-*`).

**Spec:** `docs/superpowers/specs/2026-11-24-switch-expressions-design.md`

## Global Constraints

- Work in the isolated worktree `/home/weigl/.local/share/opencode/worktree/fa2a33/switch-expressions`, branch `weigl/switch-expressions`, based on `weigl/pattern-hoisting`.
- Do not touch `weigl/pattern-hoisting` or its worktrees; that branch belongs to another task. When the pattern stack lands, rebase this branch onto the merged result.
- Commit after every task. Only push or open a PR when the user asks. Never push to `main`.
- Use the Gradle wrapper from the worktree root. Format with `./gradlew spotlessApply` before each commit; the gate is `./gradlew spotlessCheck`.
- Javadoc on every new public class and public method; slf4j `LOGGER`, no `System.out`/`System.err`.
- Tests are JUnit 5. Do not use the tags `owntest`, `interactive`, `performance`. Prover tests assume the single-threaded prover (`key.prover.parallel=false`).
- Nullness gate: `./gradlew -DENABLE_NULLNESS=true :key.core:compileTestJava`.
- This plan adds no taclets; `TestTacletEquality` must still pass unchanged (run it in Task 7).
- The pattern stack (`weigl/pattern-hoisting`) provides `Pattern`, `TypePattern`, `RecordPattern`, `AnyPattern`, `InstanceofPattern` and the binding rules; use them, do not duplicate them.

## Review Focus

- A side-effecting selector is evaluated exactly once (`switch (next())`), also when an arm throws or is not taken.
- `yield` inside an arm that also contains a loop must leave the switch, not the loop (`continue`/`break` inside an arm keep their Java meaning).
- A `when` guard must not be evaluated when the pattern of its arm does not match.
- Nested switch expressions (as values or inside other arms) must keep their evaluation order.
- `case null` and `default` must handle `null` without the reference-selector null check throwing first.
- A switch expression without `default` must be rejected unless exhaustiveness is certain; it must never leave the result temporary unassigned.

---

### Prerequisite (external repository): jmlparser `yield` under `LanguageLevel.RAW`

KeY configures jmlparser with `ParserConfiguration.LanguageLevel.RAW`, for which the fork
currently disables the `yield` production (`JavaParser#getParserForProvider` enables it only
for non-null levels with `isYieldSupported()`). Enable it for `RAW`
(`languageLevel == null || languageLevel.isYieldSupported()`) in `Contract-LIB/jmlparser`,
cover it with a parser test, release the artifact and bump `jmltk` in
`gradle/libs.versions.toml`. Without this, every test containing `yield` fails with a Java
syntax error.

---

### Task 1: `Yield` AST node and visitor plumbing

**Files:**
- Create: `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Yield.java`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/java/visitor/Visitor.java` (add `performActionOnYield(Yield)`)
- Modify: the `Visitor` implementors that handle statements (`JavaASTVisitor`, `CreatingASTVisitor`, `InnerBreakAndContinueReplacer`, `OuterBreakContinueAndReturnReplacer`, `WhileLoopTransformation`, `PrettyPrinter`; run `compileJava` and fix every other implementor)
- Test: `key.core/src/test/java/de/uka/ilkd/key/java/ast/YieldAstTest.java`

**Interfaces:**
- Consumes: `Expression`, `ExpressionJumpStatement`, `PositionInfo`, `Comment`.
- Produces: `public class Yield extends ExpressionJumpStatement` with `Yield(Expression)`, `Yield(ExtList)`, `Yield(Expression, PositionInfo, List<Comment>)`; `Visitor.performActionOnYield(Yield x)`; `PrettyPrinter` prints `yield <expr>;`.

- [ ] **Step 1: Write the failing test**

```java
@Test
void printsYieldWithItsExpression() {
    var yield = new Yield(new IntegerLiteral("10"));
    var pp = PrettyPrinter.purePrinter();
    pp.print(yield);
    assertThat(pp.result()).contains("yield").contains("10");
}
```

- [ ] **Step 2: Run it and confirm the failure**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.ast.YieldAstTest"`
Expected: FAIL to compile: `Yield` not found.

- [ ] **Step 3: Add `Yield` and the visitor methods**

`Yield` mirrors `Return` (it extends the same `ExpressionJumpStatement`), so the child/printing machinery comes from the superclass; only the visitor dispatch is new. Add the abstract method to `Visitor` and implement it in every implementor; `JavaASTVisitor` visits the expression, `PrettyPrinter` prints `yield ` + expression + `;`.

- [ ] **Step 4: Run the test and the full compile**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.ast.YieldAstTest" :key.core:compileJava`
Expected: PASS and BUILD SUCCESSFUL.

- [ ] **Step 5: Commit**

```bash
git add key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/Yield.java \
        key.core/src/main/java/de/uka/ilkd/key/java/visitor/ \
        key.core/src/test/java/de/uka/ilkd/key/java/ast/YieldAstTest.java
git commit -m "feat(ast): add Yield statement"
```

---

### Task 2: `PatternCase` branch node

**Files:**
- Create: `key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/PatternCase.java`
- Modify: `Visitor` (`performActionOnPatternCase(PatternCase)`), the 8 switch-handling files, `KeYJavaASTFactory` (add `patternCaseBlock(...)`)
- Test: `key.core/src/test/java/de/uka/ilkd/key/java/ast/PatternCaseAstTest.java`

**Interfaces:**
- Consumes: `Pattern` (`TypePattern`, `RecordPattern`, `AnyPattern`), `BranchImp`, `PositionInfo`, `Comment`.
- Produces: `public class PatternCase extends BranchImp` with `PatternCase(ImmutableList<Pattern> patterns, @Nullable Expression guard, ImmutableList<Statement> body, PositionInfo pi, List<Comment> comments)`, getters `getPatterns()`, `getGuard()`, `getStatementCount()`, `getStatementAt(int)`; `KeYJavaASTFactory.patternCaseBlock(...)`; printer output `case <pattern> [when <guard>]:`.

- [ ] **Step 1: Write the failing test**

```java
@Test
void printsPatternAndGuard() {
    var pattern = new TypePattern(new TypeRef(...), new ProgramElementName("s"));
    var arm = new PatternCase(ImmutableList.of(pattern), new BooleanLiteral(true),
            ImmutableList.of(new Return(null)), PositionInfo.UNDEFINED, List.of());
    var pp = PrettyPrinter.purePrinter();
    pp.print(arm);
    assertThat(pp.result()).contains("case").contains("when");
}
```

- [ ] **Step 2: Run it and confirm the failure**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.ast.PatternCaseAstTest"`
Expected: FAIL to compile: `PatternCase` not found.

- [ ] **Step 3: Add `PatternCase` and wire visitors/printers**

Follow `Case` for the body handling and `Break`/`Case` for the visitor dispatch. Children: patterns, optional guard, body statements.

- [ ] **Step 4: Run the tests**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.ast.PatternCaseAstTest" :key.core:compileJava`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add key.core/src/main/java/de/uka/ilkd/key/java/ast/statement/PatternCase.java \
        key.core/src/main/java/de/uka/ilkd/key/java/visitor/ \
        key.core/src/main/java/de/uka/ilkd/key/java/KeYJavaASTFactory.java \
        key.core/src/test/java/de/uka/ilkd/key/java/ast/PatternCaseAstTest.java
git commit -m "feat(ast): add pattern case branch for switch"
```

---

### Task 3: `SwitchExpression` AST node

**Files:**
- Create: `key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/SwitchExpression.java`
- Modify: `Visitor` (`performActionOnSwitchExpression`), the switch-handling visitors/printers
- Test: `key.core/src/test/java/de/uka/ilkd/key/java/ast/SwitchExpressionAstTest.java`

**Interfaces:**
- Consumes: `Expression`, `Branch` (`Case`, `Default`, `PatternCase`).
- Produces: `public class SwitchExpression extends Expression` with `SwitchExpression(PositionInfo pi, List<Comment> c, Expression selector, ImmutableList<Branch> branches)`, `getSelector()`, `getBranchCount()`, `getBranchAt(int)`, `getChildCount()`, `getChildAt(int)`.

- [ ] **Step 1: Write the failing test**

```java
@Test
void hasSelectorAndBranches() {
    var expr = new SwitchExpression(PositionInfo.UNDEFINED, List.of(),
            new IntegerLiteral("1"), ImmutableList.of(KeYJavaASTFactory.defaultBlock(new Return(null))));
    assertThat(expr.getSelector()).isNotNull();
    assertThat(expr.getBranchCount()).isEqualTo(1);
    assertThat(expr.getChildCount()).isEqualTo(2);
}
```

- [ ] **Step 2: Run it and confirm the failure**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.ast.SwitchExpressionAstTest"`
Expected: FAIL to compile: `SwitchExpression` not found.

- [ ] **Step 3: Add `SwitchExpression`**

Model it on `Conditional` (expression with operator children) and `Switch` (selector + branches). Visitors descend into the selector and branches; the printer renders `switch (…) { … }` best effort.

- [ ] **Step 4: Run the tests**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.ast.SwitchExpressionAstTest" :key.core:compileJava`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add key.core/src/main/java/de/uka/ilkd/key/java/ast/expression/SwitchExpression.java \
        key.core/src/main/java/de/uka/ilkd/key/java/visitor/ \
        key.core/src/test/java/de/uka/ilkd/key/java/ast/SwitchExpressionAstTest.java
git commit -m "feat(ast): add SwitchExpression node"
```

---

### Task 4: Converter for switch expressions, yields, and pattern labels

**Files:**
- Modify: `key.core/src/main/java/de/uka/ilkd/key/java/loader/JP2KeYConverter.java` (`visit(SwitchExpr)`, `visit(YieldStmt)`, `visit(SwitchEntry)`, pattern helper)
- Test: `key.core/src/test/java/de/uka/ilkd/key/java/SwitchExpressionConversionTest.java`

**Interfaces:**
- Consumes: jmlparser `SwitchExpr.getSelector()/getEntries()`, `SwitchEntry.getLabels()/getStatements()/getType()/getGuard()/isDefault()`, `YieldStmt.getExpression()`, `TypePatternExpr`, `RecordPatternExpr`, `MatchAllPatternExpr`; the existing pattern conversion used by `visit(InstanceOfExpr)`.
- Produces: a loaded `SwitchExpression` with `Case`/`Default`/`PatternCase` branches; `Yield` statements inside arm bodies; `reportUnsupportedElement` for constructs outside the supported set.

- [ ] **Step 1: Write the failing tests (load level)**

```java
@Test
void loadsArrowSwitchExpression(@TempDir Path dir) throws Exception {
    Files.writeString(dir.resolve("C.java"), """
            public class C { int f(int x) { return switch (x) { case 1 -> 10; default -> 0; }; } }
            """);
    KeYEnvironment.load(dir.resolve("C.java")).dispose();   // must not throw
}
```

Add the same shape for: colon arm with `yield`, block arm, `throw` arm, grouped labels, `case null, default`, type pattern, `when` guard, record pattern.

Add rejection tests: a switch expression with no `default` (e.g. `return switch (x) { case 1 -> 1; };`) and a switch expression in a non-hoistable position (see the lowering prerequisite) must fail to load with a clear message — the `KeYEnvironment.load` call throws and the message names the construct.

- [ ] **Step 2: Run them and confirm the failures**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.SwitchExpressionConversionTest"`
Expected: `SwitchExpr` unsupported for all cases; `yield` cases fail with a parse error until the jmlparser prerequisite is released; rejection tests fail (no error is produced yet).

- [ ] **Step 3: Implement the conversion**

`visit(SwitchExpr)`: build `SwitchExpression` from the selector and the entries. Normalize entries by `SwitchEntry.getType()`: `EXPRESSION` → body `List.of(new Yield(value))`, `THROWS_STATEMENT` → body with a `Throw`, `BLOCK`/`STATEMENT_GROUP` → the statements as written. Duplicate constant labels per label (as `visit(SwitchEntry)` does today). `visit(YieldStmt)` → `new Yield(accept(getExpression()))`. A private `Pattern createPattern(Expression label)` maps `TypePatternExpr`/`RecordPatternExpr`/`MatchAllPatternExpr` with the same code the `instanceof` conversion uses, and `getGuard()` becomes the `PatternCase` guard. Reject a switch expression with no `default` and no exhaustive enum/sealed selector via `reportUnsupportedElement`; reject any label kind the base branch cannot convert.

- [ ] **Step 4: Run the tests**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.SwitchExpressionConversionTest"`
Expected: PASS (loads; proof tests come with the lowering prerequisite).

- [ ] **Step 5: Commit**

```bash
git add key.core/src/main/java/de/uka/ilkd/key/java/loader/JP2KeYConverter.java \
        key.core/src/test/java/de/uka/ilkd/key/java/SwitchExpressionConversionTest.java
git commit -m "feat(loader): convert switch expressions, yields and pattern labels"
```

---

### Task 5: Built-in rule `SwitchExpressionRule` for switch expressions

**Files:**
- Create: `key.core/src/main/java/de/uka/ilkd/key/rule/SwitchExpressionRule.java`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/proof/init/JavaProfile.java` (`initBuiltInRules()`, next to `SetStatementRule.INSTANCE`)
- Test: `key.core/src/test/java/de/uka/ilkd/key/java/SwitchExpressionTest.java`

**Interfaces:**
- Consumes: `BuiltInRule`, `DefaultBuiltInRuleApp`, `Goal`, `PosInOccurrence`, `JavaTools.getActiveStatement(JavaBlock)`, `TermBuilder`, `EvaluateArgs.evaluate(Expression, List<? super LocalVariableDeclaration>, Services, ExecutionContext)`, `KeYJavaASTFactory`.
- Produces: `public final class SwitchExpressionRule implements BuiltInRule` with `public static final SwitchExpressionRule INSTANCE` and name `"Switch Expression"`; `isApplicable(Goal, PosInOccurrence)` is true iff the occurrence is top-level, not inside a transformer, and the active statement contains a `SwitchExpression`; `createApp(...)` returns `DefaultBuiltInRuleApp`; `apply(...)` returns the goal(s) with the rewritten Java block. Registered via `.prepend(SwitchExpressionRule.INSTANCE)` in `JavaProfile.initBuiltInRules()`.

- [ ] **Step 1: Write the failing proof tests**

Using the `InstanceOfPatternFlowScopingTest` harness (`KeYEnvironment.load` + `ProofStarter`), add contracts that must close:

```java
int f(int x) { return switch (x) { case 1 -> 10; default -> 0; }; }        // requires x==1, ensures \result==10
int g(int x) { switch (x) { case 1: return 1; default: return 0; } }        // control: statement already works
int h(int x) { return switch (x) { case 1: yield 10; default: yield 0; }; } // colon + yield
int t(int x) { return switch (x) { case 1 -> 10; default -> throw new IllegalArgumentException(); }; }
```

Add a selector-once test with a `static int calls; static int next(){ calls++; return 1; }` and a contract that proves `calls == 1` after `switch (next())`. Add a `case null, default` test on a `String` selector. Add a nested test (`int y = switch (a) { case 1 -> switch (b) { default -> 2; }; default -> 0; };`) and a `yield`-in-loop test (`case 1 -> { for (int i = 0; i < 2; i++) { if (i == 1) { yield 7; } } yield 1; }`) that proves the yielded value and the number of loop iterations. Add a rejection test for a switch expression that is not the first-evaluated operand of its statement (`f(g(), switch (x) { … })`): the proof must report the unsupported position.

- [ ] **Step 2: Run them and confirm the failures**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.SwitchExpressionTest"`
Expected: proofs stay open / the unsupported-position test fails because no rule applies.

- [ ] **Step 3: Implement the built-in rule**

`isApplicable` follows `SetStatementRule` (`AbstractAuxiliaryContractRule.occursNotAtTopLevelInSuccedent`, `Transformer.inTransformer`, then a check that the active statement's tree contains a `SwitchExpression`). In `apply`: (1) collect the switch expressions of the active statement in source order; (2) reject a position that is not the first-evaluated operand of the statement with a clear message; (3) create a temporary per switch expression by the `EvaluateArgs.evaluate` mechanism and a `Switch` statement whose branches assign the temporary (`Yield` → assignment + labelled `break`; `Throw` arms unchanged); (4) replace the expression in the statement by the temporary; (5) recurse for nested switch expressions; (6) build the new term with the extended Java block and split the goal as needed. Register the rule in `JavaProfile.initBuiltInRules()`.

- [ ] **Step 4: Run the tests**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.SwitchExpressionTest"`
Expected: PASS, including the selector-once, nested, `yield`-in-loop and `case null` tests, and the unsupported-position rejection.

- [ ] **Step 5: Commit**

```bash
git add key.core/src/main/java/de/uka/ilkd/key/rule/SwitchExpressionRule.java \
        key.core/src/main/java/de/uka/ilkd/key/proof/init/JavaProfile.java \
        key.core/src/test/java/de/uka/ilkd/key/java/SwitchExpressionTest.java
git commit -m "feat(rules): lower switch expressions with a built-in rule"
```

---

### Task 6: Pattern labels in the built-in rule

**Files:**
- Modify: `key.core/src/main/java/de/uka/ilkd/key/rule/SwitchExpressionRule.java`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/java/loader/JP2KeYConverter.java` (only if `PatternCase` construction needs adjustment after Task 4)
- Test: `key.core/src/test/java/de/uka/ilkd/key/java/SwitchPatternTest.java`

**Interfaces:**
- Consumes: `PatternCase.getPatterns()`, `PatternCase.getGuard()`, `InstanceofPattern`, and the pattern stack's binding rules.
- Produces: the built-in rule also lowers `PatternCase` labels — in `SwitchExpression` and in plain `Switch` statements — to an `if`-cascade: `tmp instanceof <pattern>` (or `exV instanceof <pattern>` for a statement selector) `&& <guard>`, in source order, with the arm body as the then-block. The pattern variable is in scope in the then-block through the existing `instanceof`-pattern rules. Constant `Case`s, `Default` and `case null` keep their current handling.

- [ ] **Step 1: Write the failing proof tests**

```java
int f(Object o) { switch (o) { case Integer i when i > 0: return i; default: return 0; } }   // requires o instanceof Integer && ((Integer)o) > 0, ensures \result > 0
int g(Object o) { switch (o) { case String s: return 1; default: return 0; } }              // requires o instanceof String, ensures \result == 1
int h(Object o) { return switch (o) { case Integer i -> i; default -> 0; }; }               // expression + type pattern
int r(Object o) { return switch (o) { case Point(int x, int y) -> x + y; default -> 0; }; } // record pattern
```

Add a guard-order test: a guard with a side effect must not run when the pattern does not match (`case Integer i when tick()` must not call `tick` for a `String` selector).

- [ ] **Step 2: Run them and confirm the failures**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.SwitchPatternTest"`
Expected: FAIL — patterns are not lowered (open goal or ClassCastException).

- [ ] **Step 3: Extend the built-in rule**

When the active statement contains a `Switch`/`SwitchExpression` with `PatternCase` branches, build the cascade in source order: for each `PatternCase`, an `If` with the `instanceof` pattern test (`&&` the guard) and the arm body; then the constant/default arms as today. For the expression form, assign the arm values to the result temporary as in Task 5. `case null` must be decided before the reference null check.

- [ ] **Step 4: Run the tests**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.SwitchPatternTest"`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add key.core/src/main/java/de/uka/ilkd/key/rule/SwitchExpressionRule.java \
        key.core/src/test/java/de/uka/ilkd/key/java/SwitchPatternTest.java
git commit -m "feat(rules): lower pattern labels in the switch built-in rule"
```

---

### Task 7: Coverage fixtures and documentation

**Files:**
- Move: `key.core/src/test/resources/de/uka/ilkd/key/java/coverage/rejected/switch-expression` → `supported/`
- Move: `.../rejected/switch-pattern-type` → `supported/`
- Move: `.../rejected/switch-pattern-record` → `supported/`
- Create fixtures under `.../coverage/supported/`: `switch-expression-yield`, `switch-expression-null`, `switch-pattern-guard`, `switch-pattern-statement`
- Modify (other repository): `key-docs/content/user/features/java-coverage.md`

**Interfaces:**
- Consumes: the coverage conventions (`problem.key` with `\javaSource "."`, one feature per directory).
- Produces: green `JavaFeatureCoverageTest`, unchanged `TestTacletEquality`, updated documentation rows.

- [ ] **Step 1: Move and add coverage fixtures**

Move the three directories and update their Java sources if needed so the expected behavior is the new one. Add the four new fixture directories. Run:

`./gradlew :key.core:test --tests "de.uka.ilkd.key.java.JavaFeatureCoverageTest" --tests "de.uka.ilkd.key.nparser.TestTacletEquality"`

Expected: PASS (the oracle file is unchanged because this plan adds no taclets).

- [ ] **Step 2: Update the documentation**

In `key-docs`, update the Java Coverage table: mark switch expressions and pattern matching for `switch` as supported (or partially supported, matching the actual set of accepted constructs), and keep the `switch` statement row's comments consistent.

- [ ] **Step 3: Format and commit**

```bash
./gradlew spotlessCheck
git add key.core/src/test/resources/de/uka/ilkd/key/java/coverage/
git commit -m "test: cover switch expressions and switch patterns"
```

(Commit the key-docs change separately in that repository.)

---

### Task 8: General evaluation-order linearization

**Files:**
- Modify: `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/LowerSwitchExpression.java`
- Test: `key.core/src/test/java/de/uka/ilkd/key/java/SwitchExpressionEvaluationOrderTest.java`

**Interfaces:**
- Consumes: `EvaluateArgs.evaluate` and the built-in rule from Task 5.
- Produces: switch expressions are accepted in any expression position; preceding side-effecting subexpressions of the same statement are hoisted into temporaries in evaluation order before the switch lowering.

- [ ] **Step 1: Write the failing tests**

Cases such as `int r = g() + switch (x) { … };`, `f(g(), switch (x) { … });`, `if (p() && switch (x) { … })`, each with a contract that pins the evaluation order of the side effects (counters, as in the lowering prerequisite's tests).

- [ ] **Step 2: Run them and confirm the failures**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.SwitchExpressionEvaluationOrderTest"`
Expected: FAIL with the built-in rule's "unsupported position" rejection.

- [ ] **Step 3: Linearize**

For the matched statement, walk its expression subterms in Java evaluation order up to and including each switch expression; hoist every subexpression that (a) precedes a switch expression in the order and (b) may have side effects, into temporaries via `EvaluateArgs.evaluate` (receiver, arguments, operands, condition parts). Replace them by their temporaries, then proceed as in Task 5. Remove the restriction.

- [ ] **Step 4: Run the tests and the regression suite**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.SwitchExpressionEvaluationOrderTest" --tests "de.uka.ilkd.key.java.SwitchExpressionTest" --tests "de.uka.ilkd.key.java.SwitchPatternTest"`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/LowerSwitchExpression.java \
        key.core/src/test/java/de/uka/ilkd/key/java/SwitchExpressionEvaluationOrderTest.java
git commit -m "feat(rules): linearize switch expressions in arbitrary positions"
```

---

## Final verification

- [ ] `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.Switch*" --tests "de.uka.ilkd.key.java.JavaFeatureCoverageTest" --tests "de.uka.ilkd.key.nparser.TestTacletEquality"` — PASS
- [ ] `./gradlew spotlessCheck` — PASS
- [ ] `./gradlew -DENABLE_NULLNESS=true :key.core:compileTestJava` — PASS
- [ ] `key-docs`: `make build` — PASS
- [ ] Rebase onto the merged pattern stack once it lands; rerun the above.
