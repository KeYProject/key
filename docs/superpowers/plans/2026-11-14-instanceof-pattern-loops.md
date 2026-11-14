# Pattern Bindings for `while`, `for`, and `do` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add JLS 6.3.2.3–6.3.2.5 flow scoping for `instanceof` pattern variables in `while`, `for`, and `do` statements, including JML visibility.

**Architecture:** One standalone `patternLoopUnfold` taclet rewrites a binding loop before any loop treatment: the guard is hoisted into a fresh boolean, the body gets `#posBinding` and a body-end guard refresh, target `continue`s are rewritten, and `whenFalse` declarations are appended after the loop when no unlabeled break targets it. The rewritten loop guard is a plain variable, so the rule fires exactly once and all existing loop treatments see an ordinary loop.

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

### Task 1: `isBindingLoop` condition

**Files:**
- Create: `key.core/src/main/java/de/uka/ilkd/key/rule/conditions/IsBindingLoopCondition.java`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/nparser/varexp/TacletBuilderManipulators.java`
- Test: `key.core/src/test/java/de/uka/ilkd/key/rule/conditions/IsBindingLoopConditionTest.java`

**Interfaces:**
- Consumes: `BindingVariableVisitor.binds(Expression)`, `While` / `For` / `Do` / `LoopStatement`.
- Produces: `public final class IsBindingLoopCondition implements VariableCondition`; package-visible `static boolean bindsLoop(Statement statement)`; taclet name `\isBindingLoop(#loopStmt)`.

- [ ] **Step 1: Write the failing test**

Create `IsBindingLoopConditionTest` using `HelperClassForTests.createServices()` and `KeyIO` to parse a program and extract its first statement:

```java
private static Statement firstStatement(Services services, String program) {
    JTerm term = new KeyIO(services, services.getNamespaces())
        .parseExpression("\\<{" + program + "}\\> true");
    return term.javaBlock().program().getFirstElement();
}

@Test
void detectsBindingWhile() {
    assertTrue(IsBindingLoopCondition.bindsLoop(firstStatement(services,
        "while (o instanceof String s) { }")));
}

@Test
void detectsBindingForAndDo() {
    assertTrue(IsBindingLoopCondition.bindsLoop(firstStatement(services,
        "for (; o instanceof String s; ) { }")));
    assertTrue(IsBindingLoopCondition.bindsLoop(firstStatement(services,
        "do { } while (o instanceof String s);")));
}

@Test
void rejectsPlainGuard() {
    assertFalse(IsBindingLoopCondition.bindsLoop(firstStatement(services,
        "while (o != null) { }")));
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.conditions.IsBindingLoopConditionTest" --console=plain`
Expected: FAIL with `cannot find symbol: class IsBindingLoopCondition`.

- [ ] **Step 3: Implement the condition and register it**

`IsBindingLoopCondition`:

```java
package de.uka.ilkd.key.rule.conditions;

public final class IsBindingLoopCondition implements VariableCondition {
    private final SchemaVariable loopSV;

    public IsBindingLoopCondition(SchemaVariable loopSV) {
        this.loopSV = loopSV;
    }

    static boolean bindsLoop(Statement statement) {
        return statement instanceof While w
                && BindingVariableVisitor.binds(w.getGuardExpression())
            || statement instanceof For f
                && BindingVariableVisitor.binds(f.getGuardExpression())
            || statement instanceof Do d
                && BindingVariableVisitor.binds(d.getGuardExpression());
    }

    @Override
    public MatchResultInfo check(SchemaVariable var, SyntaxElement instCandidate,
            MatchResultInfo matchCond, LogicServices services) {
        var svInst = (SVInstantiations) matchCond.getInstantiations();
        var statement = (Statement) svInst.getInstantiation(loopSV);
        return statement != null && bindsLoop(statement) ? matchCond : null;
    }

    @Override
    public String toString() {
        return "\\isBindingLoop(" + loopSV.name() + ")";
    }
}
```

Register it in `TacletBuilderManipulators` next to `BINDING_EXPRESSION_SIMPLE`:

```java
public static final TacletBuilderCommand BINDING_LOOP =
    new ConstructorBasedBuilder("isBindingLoop", IsBindingLoopCondition.class, SV);
```

- [ ] **Step 4: Run test to verify it passes**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.conditions.IsBindingLoopConditionTest" --console=plain`
Expected: PASS.

- [ ] **Step 5: Format, commit, push**

```bash
./gradlew spotlessApply
git add key.core/src/main/java/de/uka/ilkd/key/rule/conditions/IsBindingLoopCondition.java \
        key.core/src/main/java/de/uka/ilkd/key/nparser/varexp/TacletBuilderManipulators.java \
        key.core/src/test/java/de/uka/ilkd/key/rule/conditions/IsBindingLoopConditionTest.java
git commit -m "feat: add isBindingLoop taclet condition"
git push
```

---

### Task 2: `while` rewrite, `patternLoopUnfold` rule, and priority

**Files:**
- Create: `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/PatternLoopRewriter.java`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/rule/metaconstruct/ProgramTransformerRegistry.java`
- Modify: `key.core/src/main/resources/de/uka/ilkd/key/proof/rules/javaRules.key`
- Modify: `key.core/src/main/resources/de/uka/ilkd/key/proof/rules/ruleSetsDeclarations.key`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/strategy/SymExCost.java`
- Modify: `key.core/src/main/java/de/uka/ilkd/key/strategy/SymExStrategy.java`
- Test: `key.core/src/test/java/de/uka/ilkd/key/rule/TestPatternLoopRules.java`

**Interfaces:**
- Consumes: `IsBindingLoopCondition` from Task 1; `BindingVariableVisitor`, `OuterBreakContinueAndReturnCollector`, `WhileLoopTransformation`, `KeYJavaASTFactory`.
- Produces: `PatternLoopRewriter(SchemaVariable loopSV, SchemaVariable boolSV, SchemaVariable innerLabelSV, SchemaVariable outerLabelSV)` and `transform(...) -> ProgramElement[]`; taclet `patternLoopUnfold`; rule set `pattern_loop_binding`.

- [ ] **Step 1: Write the failing rule test**

Copy the fixture and helpers from `TestPatternIfRules` into `TestPatternLoopRules`, changing the rule index to `patternLoopUnfold`. The test profile must load `ruleSetsDeclarations.key` in addition to `javaRules.key` and the LDT file:

```java
private static final Profile PROFILE = new JavaProfile() {
    @Override
    public RuleCollection getStandardRules() {
        return new RuleCollection(
            ImmutableList.of(
                RuleSourceFactory.fromDefaultLocation(RuleSource.ldtFile),
                RuleSourceFactory.fromDefaultLocation("ruleSetsDeclarations.key"),
                RuleSourceFactory.fromDefaultLocation("javaRules.key")),
            ImmutableList.nil());
    }
};
```

Add the applicability and rewrite tests:

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
```

Add a continue test after the first four pass; adjust the printed braces to the actual output:

```java
@Test
void refreshesGuardBeforeContinue() {
    Goal goal = applyRule("patternLoopUnfold",
        "while (new String(\"x\") instanceof String s) { continue; }");
    String printed = ProofSaver.printAnything(
        goal.sequent().succedent().getFirst().formula(), services);
    assertTrue(printed.contains("b = new String(\"x\") instanceof String s; continue;"),
        printed);
}
```

- [ ] **Step 2: Run test to verify it fails**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.TestPatternLoopRules" --console=plain`
Expected: FAIL because `patternLoopUnfold` is not in the taclet index.

- [ ] **Step 3: Implement the `while` transformer**

Create `PatternLoopRewriter`:

```java
@TransformerMeta(name = "#rewritePatternLoop")
public final class PatternLoopRewriter extends ProgramTransformer {
    private final SchemaVariable loopSV;
    private final SchemaVariable boolSV;
    private final SchemaVariable innerLabelSV;
    private final SchemaVariable outerLabelSV;

    public PatternLoopRewriter(SchemaVariable loopSV, SchemaVariable boolSV,
            SchemaVariable innerLabelSV, SchemaVariable outerLabelSV) {
        super("#rewritePatternLoop", loopSV);
        this.loopSV = loopSV;
        this.boolSV = boolSV;
        this.innerLabelSV = innerLabelSV;
        this.outerLabelSV = outerLabelSV;
    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        return ImmutableList.of(loopSV, boolSV, innerLabelSV, outerLabelSV);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        var loop = (Statement) svInst.getInstantiation(loopSV);
        var boolVar = (ProgramVariable) svInst.getInstantiation(boolSV);
        return switch (loop) {
            case While w -> rewriteWhile(w, boolVar, services);
            case For f -> throw new UnsupportedOperationException("added in Task 3");
            case Do d -> throw new UnsupportedOperationException("added in Task 3");
            default -> new ProgramElement[] { loop };
        };
    }
}
```

Implement `rewriteWhile`:

```java
static ProgramElement[] rewriteWhile(While loop, ProgramVariable boolVar, Services services) {
    Expression guard = loop.getGuardExpression();
    Statement body = loop.getBody();
    var bindings = BindingVariableVisitor.analyze(guard);

    Statement rewrittenBody = rewriteContinues(body, boolVar, guard, List.of(), services);
    var bodyStatements = new ArrayList<Statement>();
    bodyStatements.addAll(List.of(BindingVariableVisitor.toStatements(bindings.whenTrue())));
    bodyStatements.add(rewrittenBody);
    bodyStatements.add(KeYJavaASTFactory.assign(boolVar, guard));

    While newLoop = KeYJavaASTFactory.whileLoop(boolVar,
        KeYJavaASTFactory.block(bodyStatements.toArray(Statement[]::new)),
        loop.getPositionInfo());
    copyLoopSpec(loop, newLoop, services);

    var result = new ArrayList<Statement>();
    result.add(new LocalVariableDeclaration(
        new TypeRef(services.getJavaInfo().getKeYJavaType("boolean")),
        new VariableSpecification(boolVar, guard,
            services.getJavaInfo().getKeYJavaType("boolean"))));
    result.add(newLoop);
    if (!bindings.whenFalse().isEmpty() && !hasUnlabeledBreak(body, services)) {
        result.addAll(List.of(BindingVariableVisitor.toStatements(bindings.whenFalse())));
    }
    return result.toArray(ProgramElement[]::new);
}
```

Implement the continue rewriter. It must track loop depth only (not switch depth):

```java
private static Statement rewriteContinues(Statement body, ProgramVariable boolVar,
        Expression guard, List<Statement> prefix, Services services) {
    var rewriter = new CreatingASTVisitor(body, true, services) {
        private int loopDepth = 0;

        @Override
        protected void walk(ProgramElement node) {
            if (node instanceof LoopStatement) {
                loopDepth++;
            }
            super.walk(node);
            if (node instanceof LoopStatement) {
                loopDepth--;
            }
        }

        @Override
        public void performActionOnContinue(Continue x) {
            if (loopDepth == 0 && x.getLabel() == null) {
                var stats = new ArrayList<Statement>(prefix);
                stats.add(KeYJavaASTFactory.assign(boolVar, guard));
                stats.add(new Continue(x.getPositionInfo()));
                addChild(KeYJavaASTFactory.block(
                    stats.toArray(Statement[]::new)));
                changed();
            } else {
                doDefaultAction(x);
            }
        }
    };
    rewriter.start();
    return (Statement) rewriter.result();
}
```

Implement the break check:

```java
private static boolean hasUnlabeledBreak(Statement body, Services services) {
    var collector = new OuterBreakContinueAndReturnCollector(body, List.of(), services);
    collector.collect();
    return collector.getBreaks().stream().anyMatch(b -> b.getLabel() == null);
}
```

Implement loop-spec copying using the existing `WhileLoopTransformation` pattern:

```java
static void copyLoopSpec(LoopStatement from, While to, Services services) {
    var repo = services.getSpecificationRepository();
    repo.copyLoopInvariant(from, to);
    var contracts = repo.getLoopContracts(from);
    if (contracts != null) {
        for (var contract : contracts) {
            repo.addLoopContract(contract.setLoop(to));
        }
    }
}
```

Register the transformer in `ProgramTransformerRegistry`:

```java
register(byName, PatternLoopRewriter.class);
```

- [ ] **Step 4: Add the taclet and priority**

In `javaRules.key`, add `#slist0` and `#loopStmt` to the schema declarations:

```text
\program [list] Statement #slist, #slist0, #slist1, #slist2, #slist3;
\program Statement #loopStmt;
```

Add the rule after the pattern `if` rules:

```text
patternLoopUnfold {
    \find(\modality{#allmodal}{.. { #slist0 #loopStmt #slist } ...}\endmodality (post))
    \varcond(\isBindingLoop(#loopStmt))
    \varcond(\new(#boolv, boolean))
    \varcond(\newLabel(#innerLabel), \newLabel(#outerLabel))
    \replacewith(
      \modality{#allmodal}{..
        { #slist0
          #rewritePatternLoop(#loopStmt, #boolv, #innerLabel, #outerLabel)
          #slist }
      ...}\endmodality (post))
    \heuristics(pattern_loop_binding)
    \displayname "patternLoopUnfold"
}
```

In `ruleSetsDeclarations.key`, add `pattern_loop_binding;` next to `loop_expand;`.

In `SymExCost`, add:

```java
static final long PATTERN_LOOP_BINDING = -30_000;
```

In `SymExStrategy.setupCostComputationF`, add:

```java
bindRuleSet(d, "pattern_loop_binding", longConst(PATTERN_LOOP_BINDING));
```

- [ ] **Step 5: Run the rule tests and fix the printed expectations**

Run: `./gradlew :key.core:test --tests "de.uka.ilkd.key.rule.TestPatternLoopRules" --console=plain`
Expected: PASS. If a printer difference appears (braces or the fresh name `b#0`), adjust the expected strings to the actual pretty-printed form; do not change the rule semantics.

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
- Consumes: Task 2's `rewriteWhile`, `rewriteContinues`, `hasUnlabeledBreak`, `copyLoopSpec`.
- Produces: `rewriteFor(For, ProgramVariable, Services)` and `rewriteDo(Do, ProgramVariable, ProgramElementName, ProgramElementName, Services)`.

- [ ] **Step 1: Add failing tests for `for` and `do`**

```java
@Test
void rewritesForBodyUpdateAndAfterBinding() {
    Goal goal = applyRule("patternLoopUnfold",
        "for (int i = 0; i < 1 && new String(\"x\") instanceof String s; i++) {"
            + " int y = s.length(); }"
            + " int z = s.length();");
    String printed = ProofSaver.printAnything(
        goal.sequent().succedent().getFirst().formula(), services);
    assertTrue(printed.contains("while (b)"), printed);
    assertTrue(printed.contains("s = (String) new String(\"x\")"), printed);
    assertTrue(printed.contains("int z = s.length();"), printed);
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
void rewritesDoAfterBindingOutsideFirstBody() {
    Goal goal = applyRule("patternLoopUnfold",
        "do { int y = 1; } while (!(new String(\"x\") instanceof String s));"
            + " int z = s.length();");
    String printed = ProofSaver.printAnything(
        goal.sequent().succedent().getFirst().formula(), services);
    assertTrue(printed.indexOf("int y = 1;") < printed.indexOf("java.lang.String s"),
        printed);
    assertTrue(printed.contains("int z = s.length();"), printed);
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

    List<Statement> updates = new ArrayList<>();
    for (Expression update : loop.getIForUpdates().getUpdates()) {
        updates.add(new ExpressionStatement(update));
    }

    Statement rewrittenBody =
        rewriteContinues(body, boolVar, guard, updates, services);
    var bodyStatements = new ArrayList<Statement>();
    bodyStatements.addAll(List.of(BindingVariableVisitor.toStatements(bindings.whenTrue())));
    bodyStatements.add(rewrittenBody);
    bodyStatements.addAll(updates);
    bodyStatements.add(KeYJavaASTFactory.assign(boolVar, guard));

    While newLoop = KeYJavaASTFactory.whileLoop(boolVar,
        KeYJavaASTFactory.block(bodyStatements.toArray(Statement[]::new)),
        loop.getPositionInfo());
    copyLoopSpec(loop, newLoop, services);

    var initBlock = new ArrayList<Statement>();
    for (var init : loop.getInits().getInits()) {
        initBlock.add((Statement) init);
    }
    initBlock.add(new LocalVariableDeclaration(
        new TypeRef(services.getJavaInfo().getKeYJavaType("boolean")),
        new VariableSpecification(boolVar, guard,
            services.getJavaInfo().getKeYJavaType("boolean"))));
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

Add the init-variable guard:

```java
private static boolean afterBindingsUseNoForInitVariables(For loop,
        Map<LocationVariable, Expression> whenFalse, Services services) {
    var initVars = new LinkedHashSet<LocationVariable>();
    for (var init : loop.getInits().getInits()) {
        if (init instanceof LocalVariableDeclaration decl) {
            for (var spec : decl.getVariables()) {
                initVars.add((LocationVariable) spec.getProgramVariable());
            }
        }
    }
    for (Expression expression : whenFalse.values()) {
        for (LocationVariable read : MiscTools.getLocalIns(expression, services)) {
            if (initVars.contains(read)) {
                return false;
            }
        }
    }
    return true;
}
```

- [ ] **Step 4: Implement `rewriteDo`**

Reuse the existing `doWhileUnwind` normalization:

```java
static ProgramElement[] rewriteDo(Do loop, ProgramVariable boolVar,
        ProgramElementName innerLabel, ProgramElementName outerLabel, Services services) {
    var transformation = new WhileLoopTransformation(loop, outerLabel, innerLabel, services);
    transformation.start();
    ProgramElement normalized = transformation.result();

    While generated = findFirstWhile(normalized);
    if (generated == null) {
        return new ProgramElement[] { normalized };
    }
    ProgramElement[] rewritten = rewriteWhile(generated, boolVar, services);
    var result = new ArrayList<ProgramElement>();
    result.add(normalized);
    // rewritten[0] is the boolean declaration, rewritten[1] is the new while
    result.add(rewritten[0]);
    result.add(rewritten[1]);
    for (int i = 2; i < rewritten.length; i++) {
        result.add(rewritten[i]);
    }
    return result.toArray(ProgramElement[]::new);
}
```

The generated `while` must be replaced inside the normalized block, not appended after it. Use `ProgramElementReplacer` to substitute the generated while with the new declaration + while inside `normalized`, then append only the after-loop declarations:

```java
var replacement = KeYJavaASTFactory.block(rewritten[0], rewritten[1]);
ProgramElement newNormalized = new ProgramElementReplacer(normalized, services)
    .replace(generated, replacement);
```

`findFirstWhile` walks `getChild(i)` recursively. `beforeLook`:
- the normalized block contains `firstBody`, then the generated while;
- replacing the while with `{ boolean b = guard; while (b) {...} }` keeps the first body before the declaration, so the pattern variable is not in scope in the first body;
- append `rewritten[2..]` after `newNormalized`.

Add the `ProgramElementReplacer` import from `de.uka.ilkd.key.rule.metaconstruct` (same package).

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
- Produces: proof-level regression coverage for `while`, `for`, `do`, break suppression, and the four loop treatments.

- [ ] **Step 1: Write the test fixture**

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
              @ ensures \result >= 0;
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
              @ ensures \result == ((String) o).length();
              @*/
            public static int m(Object o) {
                while (!(o instanceof String s)) { o = null; }
                return s.length();
            }
        }
        """, StrategyProperties.LOOP_SCOPE_EXPAND);
}
```

- [ ] **Step 3: Add `for`, `do`, and break cases**

```java
@Test
void forBodyAndUpdateBinding(@TempDir Path dir) throws Exception {
    prove("ForBody", """
        public class ForBody {
            /*@ normal_behavior
              @ requires true;
              @ ensures \result >= 0;
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
              @ ensures \result == ((String) o).length();
              @*/
            public static int m(Object o) {
                do { o = o; } while (!(o instanceof String s));
                return s.length();
            }
        }
        """, StrategyProperties.LOOP_SCOPE_EXPAND);
}
```

The break case is a parser/rule-level test: a `break` targeting the loop must suppress the after-loop declaration. Keep it in `TestPatternLoopRules` (Task 2) rather than writing Java source that does not compile.

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
              @ requires o instanceof String;
              @ ensures true;
              @*/
            public static void m(Object o) {
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

In `collectLocalVariablesVisibleTo`, add loop handling before the generic `StatementContainer` branch. Use a helper that treats a single-statement body as a one-statement block:

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

Add the cases:

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

`asContainer(Statement body)` returns `body instanceof StatementContainer c ? c : new StatementBlock(body)`.
For a `For`, keep the existing init-variable handling before the `s == statement` check. The after-loop variables must be added **after** the `s == statement` check, so a loop invariant does not see its own bindings.

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
- Modify: `key.core/src/test/java/de/uka/ilkd/key/rule/TestPatternLoopRules.java` (only if the oracle run exposes a missing expectation)

**Interfaces:**
- Consumes: everything from Tasks 1–5.
- Produces: a green branch with the oracle updated and a documented example.

- [ ] **Step 1: Update the taclet oracle**

Run the taclet equality test:

```bash
./gradlew :key.core:test --tests "de.uka.ilkd.key.nparser.TestTacletEquality" --console=plain
```

Copy the updated `taclets.old.txt` produced by the test or update it with the new `patternLoopUnfold` entry and the `\isBindingLoop` string. Re-run the test until it passes.

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

Add a short README section explaining that `while`/`for` bodies and after-loop `whenFalse` bindings are supported, and that `do` bodies do not see the variable.

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
- The `while` rewrite is the first deliverable; `for`/`do` follow in Task 3 because they reuse the same transformer helpers.
- The after-loop declarations are always outside the init/normalized block, so they are visible to the statements after the loop.
- The guard is a plain boolean in every rewritten loop, so `patternLoopUnfold` cannot fire again and no marker flag is needed.
- The break predicate is the same in the transformer and in `JMLSpecFactory`.
