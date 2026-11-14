# Pattern Bindings for `while`, `for`, and `do` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add JLS 6.3.2.3–6.3.2.5 flow scoping for `instanceof` pattern variables in `while`, `for`, and `do` statements, including JML visibility.

**Architecture:** Two standalone `patternLoopUnfold` taclets (root block and nested block) scan a block's direct statements with the existing `isBindingExpr` condition, now extended to accept loop statements and statement lists. A `#rewritePatternBlock` transformer rewrites the first binding loop: it hoists the guard into a fresh boolean, inserts `#posBinding` and a body-end guard refresh, rewrites target `continue`s, and appends `whenFalse` declarations after the loop when no unlabeled break targets it. The rewritten loop guard is a plain variable, so the rule fires exactly once and all existing loop treatments see an ordinary loop.

**Tech Stack:** Java 21, Gradle wrapper, KeY taclets, `ProgramTransformer` meta-constructs, JUnit 5, AssertJ.

**Spec:** `docs/superpowers/specs/2026-11-14-instanceof-pattern-loops-design.md`

## Global Constraints

- Work in the stacked worktree `/tmp/opencode/key-pr3976-loops`, branch `weigl/instanceof-loops`, based on `pr-3976`.
- Commit and push after every task. Keep the branch linear; never merge and never push to `main`.
- Use the Gradle wrapper; run tasks from the worktree root.
- All new public classes and public methods need Javadoc. Use slf4j `LOGGER`; no `System.out`/`System.err`.
- Format with `./gradlew spotlessApply` before each commit; the CI gate is `spotlessCheck`.
- Tests are JUnit 5; avoid tags `owntest`, `interactive`, `performance`.
- Prover tests assume `key.prover.parallel=false`.
- Nullness gate: `./gradlew -DENABLE_NULLNESS=true :key.core:compileTestJava`.
- Do not open a PR unless the user asks; pushing the branch is expected.

## Review Focus

- A `continue` completes an iteration: the guard must be re-evaluated before the next body, including `continue` inside a `switch` or a `try`.
- A reachable `break` targeting the loop means the loop can exit without the guard being false: no after-loop pattern declaration may be inserted.
- A `do` body runs before the guard: the pattern variable must not be bound in the first body, and after-loop bindings must sit outside the normalized `do` block.
- A `for` init variable must not leak to the enclosing block, and the update must run on `continue`; the after-loop declaration must sit outside the init-scoped block.
- Labeled loops and unbraced loop bodies are the fallback path: they must not be rewritten, and the existing `if`-based body binding must still work.

---

### Task 1: Extend `isBindingExpr` to loop guards and statement lists

**Files:**
- Modify: `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/BindingExpressionCond.java`
- Test: `key.core/src/test/java/de/uka/ilkd/key/rule/conditions/BindingExpressionCondTest.java`

**Interfaces:**
- Consumes: `BindingVariableVisitor.binds(Expression)`, `LoopStatement`, `Guard`.
- Produces: `\isBindingExpr(<sv>)` accepts an expression, a loop statement (inspects its guard), a `Guard`, or an `ImmutableArray<Statement>` (true if a direct statement is a binding loop).

- [ ] **Step 1: Write the failing test**

Create `BindingExpressionCondTest` with the fixture from `TestPatternIfRules` (a `JavaProfile` loading `ldtFile` and `javaRules.key`), `KeyIO` parsing, and these cases:

```java
@Test
void acceptsLoopStatements() {
    assertTrue(isBinding(firstStatement(
        "while (new String(\"x\") instanceof String s) { }"), false));
    assertTrue(isBinding(firstStatement(
        "for (; new String(\"x\") instanceof String s; ) { }"), false));
    assertTrue(isBinding(firstStatement(
        "do { } while (new String(\"x\") instanceof String s);"), false));
}

@Test
void rejectsPlainLoop() {
    assertFalse(isBinding(firstStatement(
        "while (new String(\"x\") != null) { }"), false));
}

@Test
void acceptsStatementListWithBindingLoop() {
    var list = new ImmutableArray<>(
        firstStatement("int x = 0;"),
        firstStatement("while (new String(\"x\") instanceof String s) { }"));
    assertTrue(isBinding(list, true));
}

@Test
void rejectsStatementListWithoutBindingLoop() {
    var list = new ImmutableArray<>(
        firstStatement("int x = 0;"),
        firstStatement("while (new String(\"x\") != null) { }"));
    assertFalse(isBinding(list, true));
}
```

The helper creates a `ProgramSV` of sort `ProgramSVSort.STATEMENT`, adding it as a list instantiation when `list` is true, wraps it in `MatchConditions`, and calls `new BindingExpressionCond(sv, false).check(...)`.

- [ ] **Step 2: Run test to verify it fails**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.conditions.BindingExpressionCondTest" --console=plain`
Expected: FAIL for `acceptsLoopStatements` and `acceptsStatementListWithBindingLoop`.

- [ ] **Step 3: Implement the unwrapping**

In `BindingExpressionCond.check`, replace the `instanceof Expression` branch with:

```java
Expression expression = null;
boolean isBindingExpr = false;

if (condition instanceof Expression e) {
    expression = e;
} else if (condition instanceof LoopStatement loop) {
    expression = loop.getGuardExpression();
} else if (condition instanceof Guard guard) {
    expression = guard.getExpression();
}

if (expression != null) {
    isBindingExpr = BindingVariableVisitor.binds(expression);
} else if (condition instanceof ImmutableArray<?> list) {
    for (Object element : list) {
        if (element instanceof LoopStatement loop
                && BindingVariableVisitor.binds(loop.getGuardExpression())) {
            isBindingExpr = true;
            break;
        }
    }
}
```

Keep `toString()` as `\isBindingExpr(<sv>)`.

- [ ] **Step 4: Run test to verify it passes**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.conditions.BindingExpressionCondTest" --console=plain`
Expected: PASS.

- [ ] **Step 5: Format, commit, push**

```bash
./gradlew spotlessApply
git add key.core/src/main/java/de/uka/ilkd/key/rule/conditions/BindingExpressionCond.java \
        key.core/src/test/java/de/uka/ilkd/key/rule/conditions/BindingExpressionCondTest.java
git commit -m "feat: extend isBindingExpr to loop guards and statement lists"
git push
```

---

### Task 2: `while` rewrite, block rules, and priority

**Files:**
- Create: `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/PatternLoopRewriter.java`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/ProgramTransformerRegistry.java`
- Modify: `key.core/src/main/resources/de/uka/ilkd/key/proof/rules/javaRules.key`
- Modify: `key.core/src/main/resources/de/uka/ilkd/key/proof/rules/ruleSetsDeclarations.key`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/strategy/SymExCost.java`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/strategy/SymExStrategy.java`
- Test: `key.core/src/test/java/de/uka/ilkd/key/rule/TestPatternLoopRules.java`

**Interfaces:**
- Consumes: `isBindingExpr` from Task 1; `BindingVariableVisitor`, `OuterBreakContinueAndReturnCollector`, `KeYJavaASTFactory`.
- Produces: `PatternLoopRewriter(ProgramElement statementsSV)` and `transform(...) -> ProgramElement[]`; meta-construct `#rewritePatternBlock`; taclets `patternLoopUnfold` (root) and `patternLoopUnfoldNested` (nested); rule set `pattern_loop_binding`.

- [ ] **Step 1: Write the failing rule test**

Copy the fixture and helpers from `TestPatternIfRules` into `TestPatternLoopRules`, adding `ruleSetsDeclarations.key` to the profile. Add:

```java
@Test
void appliesToBindingWhile() {
    List<String> rules = applicableRules(
        "while (new String(\"x\") instanceof String s) { int y = s.length(); }");
    assertTrue(rules.contains("patternLoopUnfold"), rules.toString());
}

@Test
void ignoresPlainWhile() {
    List<String> rules = applicableRules(
        "while (new String(\"x\") != null) { int y = 1; }");
    assertFalse(rules.contains("patternLoopUnfold"), rules.toString());
}

@Test
void rewritesBodyWithPositionAndGuardRefresh() {
    Goal goal = applyRule("patternLoopUnfold",
        "while (new String(\"x\") instanceof String s) { int y = s.length(); }");
    assertSuccedent(goal,
        "\\<{boolean b = new String(\"x\") instanceof String s;"
            + " while (b) { java.lang.String s = (String) new String(\"x\");"
            + " int y = s.length(); b = new String(\"x\") instanceof String s; }}\\> true");
}

@Test
void addsAfterLoopBindingForNegatedGuard() {
    Goal goal = applyRule("patternLoopUnfold",
        "while (!(new String(\"x\") instanceof String s)) { int y = 1; }"
            + " int z = s.length();");
    assertSuccedent(goal,
        "\\<{boolean b = !(new String(\"x\") instanceof String s);"
            + " while (b) { int y = 1; b = !(new String(\"x\") instanceof String s); }"
            + " java.lang.String s = (String) new String(\"x\");"
            + " int z = s.length();}\\> true");
}

@Test
void suppressesAfterLoopBindingOnBreak() {
    Goal goal = applyRule("patternLoopUnfold",
        "while (!(new String(\"x\") instanceof String s)) { break; }");
    assertSuccedent(goal,
        "\\<{boolean b = !(new String(\"x\") instanceof String s);"
            + " while (b) { break; b = !(new String(\"x\") instanceof String s); }}\\> true");
}

@Test
void refreshesGuardBeforeContinue() {
    Goal goal = applyRule("patternLoopUnfold",
        "while (new String(\"x\") instanceof String s) { continue; }");
    String printed = ProofSaver.printAnything(
        goal.sequent().succedent().getFirst().formula(), services);
    assertTrue(printed.matches(
        "(?s).*b = new String\\(\"x\"\\) instanceof String s;\\s+continue;.*"), printed);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.TestPatternLoopRules" --console=plain`
Expected: FAIL because `patternLoopUnfold` is not in the taclet index.

- [ ] **Step 3: Implement the block transformer**

Create `PatternLoopRewriter`:

```java
@TransformerMeta(name = "#rewritePatternBlock")
public final class PatternLoopRewriter extends ProgramTransformer {
    private final SchemaVariable statementsSV;

    public PatternLoopRewriter(ProgramElement statementsSV) {
        super("#rewritePatternBlock", statementsSV);
        this.statementsSV = (SchemaVariable) statementsSV;
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of((ProgramElement) statementsSV);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        var statements = (ImmutableArray<Statement>) svInst.getInstantiation(statementsSV);
        var boolVar = freshBoolean(services);
        var result = new ArrayList<Statement>();
        boolean rewritten = false;
        for (Statement statement : statements) {
            if (!rewritten && statement instanceof LoopStatement loop
                    && BindingVariableVisitor.binds(loop.getGuardExpression())) {
                for (ProgramElement element : rewriteLoop(loop, boolVar, services)) {
                    result.add((Statement) element);
                }
                rewritten = true;
            } else {
                result.add(statement);
            }
        }
        if (!rewritten) {
            var unchanged = new ProgramElement[statements.size()];
            for (int i = 0; i < statements.size(); i++) {
                unchanged[i] = statements.get(i);
            }
            return unchanged;
        }
        return result.toArray(ProgramElement[]::new);
    }

    private static ProgramElement[] rewriteLoop(LoopStatement loop, ProgramVariable boolVar,
            Services services) {
        if (loop instanceof While whileLoop) {
            return rewriteWhile(whileLoop, boolVar, services);
        }
        throw new UnsupportedOperationException(
            "Unsupported loop kind in #rewritePatternBlock: " + loop.getClass().getSimpleName());
    }
}
```

Add `freshBoolean`:

```java
private static ProgramVariable freshBoolean(Services services) {
    var booleanType = services.getJavaInfo().getKeYJavaType("boolean");
    var name = new ProgramElementName(services.getTermBuilder().newName("b"));
    var variable = new LocationVariable(name, new TypeRef(booleanType));
    services.getNamespaces().programVariables().addSafely(variable);
    return variable;
}
```

Implement `rewriteWhile`:

```java
static ProgramElement[] rewriteWhile(While loop, ProgramVariable boolVar, Services services) {
    Expression guard = loop.getGuardExpression();
    Statement body = loop.getBody();
    var bindings = BindingVariableVisitor.analyze(guard);
    Expression strippedGuard = stripPatterns(guard, services);

    Statement rewrittenBody =
        rewriteContinues(body, boolVar, strippedGuard, List.of(), services);
    var bodyStatements = new ArrayList<Statement>();
    bodyStatements.addAll(List.of(BindingVariableVisitor.toStatements(bindings.whenTrue())));
    addBodyStatements(bodyStatements, rewrittenBody);
    bodyStatements.add(KeYJavaASTFactory.assign(boolVar, strippedGuard));

    While newLoop = KeYJavaASTFactory.whileLoop(boolVar,
        KeYJavaASTFactory.block(bodyStatements.toArray(Statement[]::new)),
        loop.getPositionInfo());
    copyLoopSpec(loop, newLoop, services);

    var result = new ArrayList<Statement>();
    result.add(booleanDeclaration(boolVar, guard, services));
    result.add(newLoop);
    if (!bindings.whenFalse().isEmpty() && !hasUnlabeledBreak(body, services)) {
        result.addAll(List.of(BindingVariableVisitor.toStatements(bindings.whenFalse())));
    }
    return result.toArray(ProgramElement[]::new);
}
```

`addBodyStatements` flattens a `StatementBlock` body into the loop body. `booleanDeclaration` creates `boolean b = guard;` from the original guard. `stripPatterns` replaces each `InstanceofPattern` by a plain `Instanceof` for the body-end and continue refresh; otherwise the loop rule's `getLocalOuts` sees two declarations of the pattern variable. `copyLoopSpec` copies the invariant and loop contracts. `rewriteContinues` uses a `CreatingASTVisitor` that replaces unlabeled continues at loop depth 0 with `{ b = strippedGuard; continue; }` and leaves nested loops and labeled continues alone. `hasUnlabeledBreak` uses `OuterBreakContinueAndReturnCollector`.

Register the transformer in `ProgramTransformerRegistry`:

```java
register(byName, PatternLoopRewriter.class);
```

- [ ] **Step 4: Add the two taclets and priority**

In `javaRules.key`, add the root and nested rules:

```text
patternLoopUnfold {
  \find(\modality{#allmodal}{ #slist }\endmodality (post))
  \varcond(\isBindingExpr(#slist))
  \replacewith(\modality{#allmodal}{ #rewritePatternBlock(#slist) }\endmodality (post))
  \heuristics(pattern_loop_binding)
  \displayname "patternLoopUnfold"
}

patternLoopUnfoldNested {
  \find(\modality{#allmodal}{.. { #slist } ...}\endmodality (post))
  \varcond(\isBindingExpr(#slist))
  \replacewith(
    \modality{#allmodal}{.. { #rewritePatternBlock(#slist) } ...}\endmodality (post))
  \heuristics(pattern_loop_binding)
  \displayname "patternLoopUnfoldNested"
}
```

In `ruleSetsDeclarations.key`, add `pattern_loop_binding;` next to `loop_expand;`. In `SymExCost`, add `PATTERN_LOOP_BINDING = -30_000;`. In `SymExStrategy.setupCostComputationF`, add:

```java
bindRuleSet(d, "pattern_loop_binding", longConst(PATTERN_LOOP_BINDING));
```

- [ ] **Step 5: Run the rule tests and fix the printed expectations**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.TestPatternLoopRules" --console=plain`
Expected: PASS. Adjust only printed-brace expectations if a printer difference appears.

- [ ] **Step 6: Format, commit, push**

```bash
./gradlew spotlessApply
git add key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/PatternLoopRewriter.java \
        key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/ProgramTransformerRegistry.java \
        key.core/src/main/java/de/uka/ilkd/key/strategy/SymExCost.java \
        key.core/src/main/java/de/uka/ilkd/key/strategy/SymExStrategy.java \
        key.core/src/main/resources/de/uka/ilkd/key/proof/rules/javaRules.key \
        key.core/src/main/resources/de/uka/ilkd/key/proof/rules/ruleSetsDeclarations.key \
        key.core/src/test/java/de/uka/ilkd/key/rule/TestPatternLoopRules.java
git commit -m "feat: rewrite pattern while loops before loop treatment"
git push
```

---

### Task 3: `for` and `do` rewrite

**Files:**
- Modify: `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/PatternLoopRewriter.java`
- Test: `key.core/src/test/java/de/uka/ilkd/key/rule/TestPatternLoopRules.java`

**Interfaces:**
- Consumes: Task 2's `rewriteWhile`, `rewriteContinues`, `hasUnlabeledBreak`, `copyLoopSpec`, `freshBoolean`.
- Produces: `rewriteFor(For, ProgramVariable, Services)` and `rewriteDo(Do, Services)`; both return `ProgramElement[]` and are dispatched from `rewriteLoop`.

- [ ] **Step 1: Add failing tests for `for` and `do`**

```java
@Test
void rewritesForBodyAndUpdate() {
    Goal goal = applyRule("patternLoopUnfold",
        "for (int i = 0; i < 1 && new String(\"x\") instanceof String s; i++) {"
            + " int y = s.length(); }");
    String printed = ProofSaver.printAnything(
        goal.sequent().succedent().getFirst().formula(), services);
    assertTrue(printed.contains("while (b)"), printed);
    assertTrue(printed.contains("s = (String) new String(\"x\")"), printed);
}

@Test
void doesNotLeakForInitVariables() {
    Goal goal = applyRule("patternLoopUnfold",
        "for (int i = 0; i < 1 && new String(\"x\") instanceof String s; i++) { }");
    String printed = ProofSaver.printAnything(
        goal.sequent().succedent().getFirst().formula(), services);
    assertTrue(printed.contains("int i = 0;"), printed);
}

@Test
void rewritesDoBodyButNotFirstBody() {
    Goal goal = applyRule("patternLoopUnfold",
        "do { int y = 1; } while (!(new String(\"x\") instanceof String s));");
    String printed = ProofSaver.printAnything(
        goal.sequent().succedent().getFirst().formula(), services);
    assertTrue(printed.indexOf("int y = 1;") < printed.indexOf("java.lang.String s"),
        printed);
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.TestPatternLoopRules" --console=plain`
Expected: FAIL with `UnsupportedOperationException` for `For`/`Do`.

- [ ] **Step 3: Implement `rewriteFor`**

```java
static ProgramElement[] rewriteFor(For loop, ProgramVariable boolVar, Services services) {
    Expression guard = loop.getGuardExpression();
    Statement body = loop.getBody();
    var bindings = BindingVariableVisitor.analyze(guard);
    Expression strippedGuard = stripPatterns(guard, services);

    List<Statement> updates = new ArrayList<>();
    var updateExpressions = loop.getUpdates();
    if (updateExpressions != null) {
        for (Expression update : updateExpressions) {
            updates.add((ExpressionStatement) update);
        }
    }

    Statement rewrittenBody =
        rewriteContinues(body, boolVar, strippedGuard, updates, services);
    var bodyStatements = new ArrayList<Statement>();
    bodyStatements.addAll(List.of(BindingVariableVisitor.toStatements(bindings.whenTrue())));
    addBodyStatements(bodyStatements, rewrittenBody);
    bodyStatements.addAll(updates);
    bodyStatements.add(KeYJavaASTFactory.assign(boolVar, strippedGuard));

    While newLoop = KeYJavaASTFactory.whileLoop(boolVar,
        KeYJavaASTFactory.block(bodyStatements.toArray(Statement[]::new)),
        loop.getPositionInfo());
    copyLoopSpec(loop, newLoop, services);

    var initBlock = new ArrayList<Statement>();
    for (var init : loop.getInits().getInits()) {
        initBlock.add((Statement) init);
    }
    initBlock.add(booleanDeclaration(boolVar, guard, services));
    initBlock.add(newLoop);

    var result = new ArrayList<Statement>();
    result.add(KeYJavaASTFactory.block(initBlock.toArray(Statement[]::new)));
    if (!bindings.whenFalse().isEmpty()
            && !hasUnlabeledBreak(body, services)
            && afterBindingsUseNoForInitVariables(loop, bindings.whenFalse(), services)) {
        result.addAll(List.of(BindingVariableVisitor.toStatements(bindings.whenFalse())));
    }
    return result.toArray(ProgramElement[]::new);
}
```

Add the init-variable guard using `MiscTools.getLocalIns` on each `whenFalse` expression and the for-init variables.

- [ ] **Step 4: Implement `rewriteDo`**

Reuse `WhileLoopTransformation` with fresh labels created by the transformer:

```java
static ProgramElement[] rewriteDo(Do loop, Services services) {
    var inner = new ProgramElementName(services.getTermBuilder().newName("inner"));
    var outer = new ProgramElementName(services.getTermBuilder().newName("outer"));
    var transformation = new WhileLoopTransformation(loop, outer, inner, services);
    transformation.start();
    ProgramElement normalized = transformation.result();
    While generated = findFirstWhile(normalized);
    if (generated == null) {
        return new ProgramElement[] { normalized };
    }
    var boolVar = freshBoolean(services);
    ProgramElement[] rewritten = rewriteWhile(generated, boolVar, services);
    var replacement = KeYJavaASTFactory.block(rewritten[0], rewritten[1]);
    ProgramElement newNormalized = new ProgramElementReplacer(normalized, services)
            .replace(generated, replacement);
    var result = new ArrayList<ProgramElement>();
    result.add(newNormalized);
    for (int i = 2; i < rewritten.length; i++) {
        result.add(rewritten[i]);
    }
    return result.toArray(ProgramElement[]::new);
}
```

Update `rewriteLoop` to dispatch `For` and `Do`. `findFirstWhile` walks children and returns the first `While`.

- [ ] **Step 5: Run the tests**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.TestPatternLoopRules" --console=plain`
Expected: PASS. Adjust only printed-brace expectations if needed.

- [ ] **Step 6: Format, commit, push**

```bash
./gradlew spotlessApply
git add key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/PatternLoopRewriter.java \
        key.core/src/test/java/de/uka/ilkd/key/rule/TestPatternLoopRules.java
git commit -m "feat: support pattern bindings in for and do loops"
git push
```

---

### Task 4: End-to-end proof tests for loop flow scoping

**Files:**
- Create: `key.core/src/test/java/de/uka/ilkd/key/java/InstanceOfPatternLoopScopingTest.java`

**Interfaces:**
- Consumes: the production rules and transformer from Tasks 1–3.
- Produces: proof-level coverage for `while`, `for`, `do`, break suppression, nested blocks, and the loop treatments.

- [ ] **Step 1: Write the fixture**

Use `KeYEnvironment.load(Path)` and `ProofStarter` like `InstanceOfPatternFlowScopingTest`. Add a helper that selects the loop treatment:

```java
private void prove(String className, String source, String loopOption) throws Exception {
    Path file = tempDir.resolve(className + ".java");
    Files.writeString(file, source);
    KeYEnvironment<?> environment = KeYEnvironment.load(file);
    try {
        var contract = environment.getProofContracts().getFirst();
        Proof proof = environment.createProof(contract.createProofObl(environment.getInitConfig()));
        var props = proof.getSettings().getStrategySettings().getActiveStrategyProperties();
        props.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, loopOption);
        proof.setActiveStrategy(proof.getActiveStrategyFactory().create(proof, props));
        ProofStarter starter = new ProofStarter(false);
        starter.init(proof);
        starter.start();
        assertTrue(proof.closed(), () -> "Open goals: " + proof.openGoals());
    } finally {
        environment.dispose();
    }
}
```

- [ ] **Step 2: Add the `while` cases**

```java
@Test
void whileBodyBinding(@TempDir Path dir) throws Exception {
    prove("WhileBody", """
        public class WhileBody {
            /*@ normal_behavior
              @ requires true;
              @ ensures \\result >= 0;
              @*/
            public static int m(Object o) {
                int n = 0;
                while (o instanceof String s) {
                    n += s.length();
                    o = null;
                }
                return n;
            }
        }
        """, StrategyProperties.LOOP_SCOPE_EXPAND);
}

@Test
void whileAfterBinding(@TempDir Path dir) throws Exception {
    prove("WhileAfter", """
        public class WhileAfter {
            /*@ normal_behavior
              @ requires o instanceof String;
              @ ensures \\result == ((String) o).length();
              @*/
            public static int m(Object o) {
                while (!(o instanceof String s)) { o = null; }
                return s.length();
            }
        }
        """, StrategyProperties.LOOP_SCOPE_EXPAND);
}
```

- [ ] **Step 3: Add `for`, `do`, and nested-block cases**

```java
@Test
void forBodyAndUpdateBinding(@TempDir Path dir) throws Exception {
    prove("ForBody", """
        public class ForBody {
            /*@ normal_behavior
              @ requires true;
              @ ensures \\result >= 0;
              @*/
            public static int m(Object o) {
                int n = 0;
                for (; o instanceof String s; o = null) {
                    n += s.length();
                }
                return n;
            }
        }
        """, StrategyProperties.LOOP_SCOPE_EXPAND);
}

@Test
void doAfterBinding(@TempDir Path dir) throws Exception {
    prove("DoAfter", """
        public class DoAfter {
            /*@ normal_behavior
              @ requires o instanceof String;
              @ ensures \\result == ((String) o).length();
              @*/
            public static int m(Object o) {
                do { o = o; } while (!(o instanceof String s));
                return s.length();
            }
        }
        """, StrategyProperties.LOOP_SCOPE_EXPAND);
}

@Test
void nestedBlockBinding(@TempDir Path dir) throws Exception {
    prove("NestedBlock", """
        public class NestedBlock {
            /*@ normal_behavior
              @ requires true;
              @ ensures \\result >= 0;
              @*/
            public static int m(Object o) {
                int n = 0;
                if (o != null) {
                    while (o instanceof String s) {
                        n += s.length();
                        o = null;
                    }
                }
                return n;
            }
        }
        """, StrategyProperties.LOOP_SCOPE_EXPAND);
}
```

The break case stays in `TestPatternLoopRules` (Task 2) because a Java source that uses the variable after a breaking loop does not compile.

- [ ] **Step 4: Run the tests**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.InstanceOfPatternLoopScopingTest" --console=plain`
Expected: PASS. If the default harness does not enable the loop rule set, create the proof from a `.key` project file with the standard settings, following `TestProofStarter`; do not weaken the assertion.

- [ ] **Step 5: Commit and push**

```bash
./gradlew spotlessApply
git add key.core/src/test/java/de/uka/ilkd/key/java/InstanceOfPatternLoopScopingTest.java
git commit -m "test: prove flow scoping for pattern loops"
git push
```

---

### Task 5: JML visibility inside and after loops

**Files:**
- Modify: `key.core/src/main/java/de/uka/ilkd/key/speclang/jml/translation/JMLSpecFactory.java`
- Test: `key.core/src/test/java/de/uka/ilkd/key/java/InstanceOfPatternLoopJmlTest.java`

**Interfaces:**
- Consumes: `BindingVariableVisitor.analyze`, the unlabeled-break helper.
- Produces: loop cases in `collectLocalVariablesVisibleTo`; JML assertions on pattern variables inside `while`/`for` bodies and after all three loops.

- [ ] **Step 1: Write the failing JML test**

```java
@Test
void assertInsideWhileBody(@TempDir Path dir) throws Exception {
    prove("WhileJmlBody", """
        public class WhileJmlBody {
            /*@ normal_behavior
              @ requires true;
              @ ensures true;
              @*/
            public static void m(Object o) {
                while (o instanceof String s) {
                    //@ assert s != null;
                    o = null;
                }
            }
        }
        """, StrategyProperties.LOOP_SCOPE_EXPAND);
}

@Test
void assertAfterWhile(@TempDir Path dir) throws Exception {
    prove("WhileJmlAfter", """
        public class WhileJmlAfter {
            /*@ normal_behavior
              @ requires true;
              @ ensures true;
              @*/
            public static void m() {
                Object o = new String("x");
                while (!(o instanceof String s)) { o = null; }
                //@ assert s != null;
            }
        }
        """, StrategyProperties.LOOP_SCOPE_EXPAND);
}
```

Add analogous tests for a `for` body and a `do` after-loop assertion.

- [ ] **Step 2: Run test to verify it fails**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.InstanceOfPatternLoopJmlTest" --console=plain`
Expected: FAIL at load time with `Cannot resolve 's'` for the body assertion.

- [ ] **Step 3: Implement loop visibility**

In `collectLocalVariablesVisibleTo`, add helpers:

```java
private ImmutableList<LocationVariable> patternVariables(boolean positive, Expression guard) {
    var bindings = BindingVariableVisitor.analyze(guard);
    return ImmutableList.fromList(
        positive ? bindings.whenTrue().keySet() : bindings.whenFalse().keySet());
}

private static boolean hasUnlabeledBreak(Statement body, Services services) {
    var collector = new OuterBreakContinueAndReturnCollector(body, List.of(), services);
    collector.collect();
    return collector.getBreaks().stream().anyMatch(b -> b.getLabel() == null);
}

private ImmutableList<LocationVariable> afterLoopVariables(LoopStatement loop) {
    if (hasUnlabeledBreak(loop.getBody(), services)) {
        return ImmutableList.nil();
    }
    return patternVariables(false, loop.getGuardExpression());
}
```

Add the loop cases before the generic `StatementContainer` branch:

```java
} else if (s instanceof While w) {
    var visible = collectLocalVariablesVisibleTo(statement, asContainer(w.getBody()));
    if (visible != null) {
        result = result.prepend(visible);
        result = result.prepend(patternVariables(true, w.getGuardExpression()));
        return result;
    }
    result = result.prepend(afterLoopVariables(w));
} else if (s instanceof For f) {
    var visible = collectLocalVariablesVisibleTo(statement, asContainer(f.getBody()));
    if (visible != null) {
        result = result.prepend(visible);
        result = result.prepend(patternVariables(true, f.getGuardExpression()));
        return result;
    }
    result = result.prepend(afterLoopVariables(f));
} else if (s instanceof Do d) {
    var visible = collectLocalVariablesVisibleTo(statement, asContainer(d.getBody()));
    if (visible != null) {
        return result.prepend(visible);
    }
    result = result.prepend(afterLoopVariables(d));
}
```

`asContainer(Statement body)` returns `body instanceof StatementContainer c ? c : new StatementBlock(body)`. For a `For`, keep the existing init-variable handling before the `s == statement` check. Add after-loop variables only after that check, so an invariant does not see its own bindings.

- [ ] **Step 4: Run the JML tests**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.java.InstanceOfPatternLoopJmlTest" --console=plain`
Expected: PASS.

- [ ] **Step 5: Run the existing JML tests**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.speclang.*" --console=plain`
Expected: PASS.

- [ ] **Step 6: Commit and push**

```bash
./gradlew spotlessApply
git add key.core/src/main/java/de/uka/ilkd/key/speclang/jml/translation/JMLSpecFactory.java \
        key.core/src/test/java/de/uka/ilkd/key/java/InstanceOfPatternLoopJmlTest.java
git commit -m "feat: expose pattern variables to JML in loops"
git push
```

---

### Task 6: Taclet oracle, example project, and full verification

**Files:**
- Modify: `key.core/src/test/resources/de/uka/ilkd/key/nparser/taclets.old.txt`
- Modify: `key.ui/examples/Java/InstanceOfPattern/src/InstanceOfPatternExample.java`
- Modify: `key.ui/examples/Java/InstanceOfPattern/README.txt`
- Modify: `key.core/src/test/java/de/uka/ilkd/key/proof/runallproofs/ProofCollections.java`

**Interfaces:**
- Consumes: everything from Tasks 1–5.
- Produces: a green branch with the oracle updated and a documented example.

- [ ] **Step 1: Update the taclet oracle**

Run the taclet equality test:

```bash
./gradlew :key.core:test --tests "de.uka.ilkd.key.nparser.TestTacletEquality" --console=plain
```

Copy the updated `taclets.old.txt` produced by the test or update it with the new `patternLoopUnfold` / `patternLoopUnfoldNested` entries. Re-run until it passes.

- [ ] **Step 2: Extend the example project**

Add methods to `InstanceOfPatternExample.java`:

```java
/*@ normal_behavior
  @ requires true;
  @ ensures \result >= 0;
  @*/
public static int whilePattern(Object obj) {
    int n = 0;
    while (obj instanceof String s) {
        n += s.length();
        obj = null;
    }
    return n;
}

/*@ normal_behavior
  @ requires obj instanceof String;
  @ ensures \result >= 0;
  @*/
public static int afterLoopPattern(Object obj) {
    while (!(obj instanceof String s)) {
        obj = null;
    }
    return s.length();
}
```

Add a short README section explaining that `while`/`for` bodies and after-loop `whenFalse` bindings are supported, and that `do` bodies do not see the variable. Register the example project in the `JavaFeatures` group of `ProofCollections.automaticJavaDL()`:

```java
g.loadable("Java/InstanceOfPattern/project.key");
```

- [ ] **Step 3: Run the targeted suites**

```bash
./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.TestPatternLoopRules" \
  --tests "de.uka.ilkd.key.java.InstanceOfPatternLoopScopingTest" \
  --tests "de.uka.ilkd.key.java.InstanceOfPatternLoopJmlTest" \
  --tests "de.uka.ilkd.key.rule.TestPatternIfRules" \
  --tests "de.uka.ilkd.key.rule.TestPatternAssignmentRules" \
  --console=plain
```

Expected: PASS.

- [ ] **Step 4: Run formatting and nullness**

```bash
./gradlew spotlessCheck
./gradlew -DENABLE_NULLNESS=true :key.core:compileTestJava
```

Expected: both succeed.

- [ ] **Step 5: Commit, push, and report**

```bash
git add key.core/src/test/resources/de/uka/ilkd/key/nparser/taclets.old.txt \
        key.ui/examples/Java/InstanceOfPattern/src/InstanceOfPatternExample.java \
        key.ui/examples/Java/InstanceOfPattern/README.txt
git commit -m "test: update taclet oracle and loop examples"
git push
```

Report the branch, the pushed head, the targeted test results, and any remaining limitation. Do not open a PR unless asked.

---

## Self-Review Notes

- Spec coverage: Tasks 2–4 cover the rewrite and flow scoping; Task 5 covers JML; Task 6 covers the oracle, examples, and verification.
- The root and nested rules both use the existing `isBindingExpr` condition, extended to loop statements and statement lists.
- The after-loop declarations are spliced into the same block list, so they are visible to the statements after the loop.
- The guard is a plain boolean in every rewritten loop, so the rewrite cannot fire again and no marker flag is needed.
- The break predicate is the same in the transformer and in `JMLSpecFactory`.
