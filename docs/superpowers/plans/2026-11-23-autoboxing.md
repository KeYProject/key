# Autoboxing and Unboxing Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (- [ ]) syntax for tracking.

**Goal:** Implement Java boxing and unboxing (JLS 5.1.7/5.1.8) for all eight wrapper types and all supported conversion contexts, with null unboxing splitting like a field access.

**Architecture:** A new JavaParser AST transformation (AutoboxingTransformer) in KeYJavaPipeline rewrites conversion contexts. Boxing becomes Wrapper.valueOf(...); unboxing becomes a read of the wrapper's final value field, which reuses the existing field-access rules and therefore produces the happy-path + null-obligation split. JavaRedux wrapper models are completed to support the generated calls and field reads. A committed semantic corpus is executed both by real Java (javac/java) and by KeY, and the two verdicts are compared.

**Tech Stack:** Java 21, Gradle wrapper, JavaParser (io.github.jmltoolkit:jmlparser-core 1.0.1), JUnit 5, AssertJ, javac/java 21.

**Spec:** docs/superpowers/specs/2026-11-23-autoboxing-design.md

## Global Constraints

- Work on branch weigl/autoboxing, based on origin/main; keep history linear; never merge.
- Use the Gradle wrapper and Java 21.
- Run ./gradlew spotlessApply before every commit; the CI gate is ./gradlew spotlessCheck.
- Nullness gate: ./gradlew -DENABLE_NULLNESS=true :key.core:compileTestJava.
- Tests are JUnit 5 (Jupiter) with AssertJ; avoid tags owntest, interactive, performance.
- Prover tests assume key.prover.parallel=false.
- Public classes and public methods need Javadoc; use slf4j LOGGER, never System.out/System.err.
- Commit after every task. Do not push and do not open a PR unless the user asks.
- JML-specification expressions and string concatenation are explicitly out of scope.
- Every semantic case added to the corpus must run under javac/java 21 and under KeY. Value semantics must agree. Reference identity and valueOf caching are recorded as known divergences.

## Design Decisions (resolved)

- Boxing is desugared to Wrapper.valueOf(widenedExpression).
- Unboxing is desugared to a read of the wrapper's final value field: expression.value. This deliberately reuses the field-access rules, which already produce the requested split: a happy-path subgoal plus a second subgoal requiring the receiver to be non-null (or a NullPointerException branch when runtime exceptions are allowed).
- Primitive widening is made explicit with a cast before boxing and after unboxing when the primitive types differ.
- JavaRedux gains a complete model per wrapper (value field, valueOf, primValue, nullable TYPE).
- The transformer runs immediately after RecordClassBuilder and before JMLTransformer, and skips JML-specification subtrees.
- Java-vs-KeY cross-check: a committed corpus is executed by javac/java 21 and by KeY; cases are recorded as PROVABLE or SPLIT.

## Review Focus

- Null unboxing must split, not silently verify: Integer a = null; int i = a; must leave the null obligation (or NPE branch).
- Two boxed operands compared with == / != must stay reference equality; only a boxed-versus-primitive comparison unboxes.
- Long l = 1 is illegal Java and must stay unconverted; boxing never widens first (Long l = 1L boxes, long x = intObj unboxes then widens).
- Varargs must box/unbox every element, including the zero-argument and exact-arity cases.
- Boxed increment/decrement nested among other side-effecting expressions must preserve left-to-right evaluation and single evaluation.
- Float/Double valueOf must handle NaN, so their specs must not use plain ==.
- The uninitialized static TYPE field must be nullable, otherwise every valueOf call leaves a static-invariant goal.
- The transformer must be idempotent and must not rewrite JML specifications or its own inserted calls.
- Java and KeY must agree on every corpus case except the explicitly recorded identity/caching divergences.

## File Structure

- Create: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/WrapperType.java
- Create: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformer.java
- Create: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java
- Modify: key.core/src/main/java/de/uka/ilkd/key/java/transformations/KeYJavaPipeline.java
- Create: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Byte.java
- Create: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Short.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Long.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Float.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Double.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Boolean.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Character.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Integer.java
- Create: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus/cases.tsv
- Create: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus/<case>/<Case>.java and expected.txt
- Create: script/autoboxing/check_java_semantics.sh
- Create: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingSemanticsTest.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingWrapperModelTest.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java
- Modify: key.core/src/test/resources/de/uka/ilkd/key/java/coverage/README.md

---

### Task 1: Complete the JavaRedux wrapper models

**Files:**
- Create: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Byte.java
- Create: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Short.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Long.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Float.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Double.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Boolean.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Character.java
- Modify: key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux/java/lang/Integer.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingWrapperModelTest.java

**Interfaces:**
- Produces: for every java.lang wrapper W a spec-public final primitive field value, a static valueOf(prim) contract, a primValue() contract, and a nullable static TYPE. Tasks 2-9 rely on value and valueOf existing for all eight wrappers.

- [ ] **Step 1: Write the failing proof test**

Create AutoboxingWrapperModelTest with a helper that writes a source string into a temp directory, selects the contract by method name, and asserts the proof closes (same harness as InstanceOfPatternFlowScopingTest). Add one case per wrapper and a TYPE case:

    public class IntModel {
        /*@ normal_behavior requires true; ensures true; @*/
        public static void m() {
            Integer a = Integer.valueOf(42);
            int i = a.value;
            //@ assert i == 42;
        }
    }

Analogous cases: Long.valueOf(42L) with a long value; Byte.valueOf((byte) 42) with byte; Short.valueOf((short) 42) with short; Character.valueOf('a') with char; Boolean.valueOf(true) with boolean; Float.valueOf(1.5f) with float; Double.valueOf(1.5d) with double. Add the TYPE case:

    Integer a = Integer.valueOf(42);
    //@ assert a != null;

- [ ] **Step 2: Run the test to verify it fails**

Run: ./gradlew :key.core:test --tests "de.uka.ilkd.key.java.AutoboxingWrapperModelTest" --console=plain

Expected: FAIL - Byte and Short are unresolved, Long.valueOf is unresolved, and the Integer.TYPE proof leaves a static-invariant goal.

- [ ] **Step 3: Implement the wrapper models**

Add to each wrapper, following Integer.java's style:

    private /*@ spec_public @*/ final <prim> value;
    public /*@ nullable @*/ final static java.lang.Class TYPE;

    /*@ public normal_behavior
      @ ensures \result.value == v;
      @ assignable \nothing;
      @*/
    public static java.lang.<Wrapper> valueOf(<prim> v);

    /*@ public normal_behavior
      @ ensures \result == value;
      @ assignable \strictly_nothing;
      @*/
    public <prim> <prim>Value();

For Float and Double specify valueOf with the existing _isSame model method (Float._isSame(\result.value, v)) so NaN is handled. Add Byte and Short as new files and complete the others.

- [ ] **Step 4: Run the test to verify it passes**

Run: ./gradlew :key.core:test --tests "de.uka.ilkd.key.java.AutoboxingWrapperModelTest" --console=plain

Expected: PASS.

- [ ] **Step 5: Run the feature coverage regression**

Run: ./gradlew :key.core:test --tests "de.uka.ilkd.key.java.JavaFeatureCoverageTest" --console=plain

Expected: PASS (no supported fixture regresses).

- [ ] **Step 6: Verify the wrapper semantics in Java (javac/jshell) and in KeY**

Gather one tiny example per wrapper in a scratch directory and validate both sides before committing:

    jshell> Integer a = 42; int i = a; i                        // -> 42
    jshell> Integer n = null; int j = n;                        // -> NullPointerException
    jshell> Long l = Long.valueOf(1L); long v = l; v            // -> 1
    jshell> Float.valueOf(Float.NaN).floatValue()               // -> NaN

Run the same value assertions through KeY (AutoboxingWrapperModelTest) and confirm both agree. Record the observed Java output and the identity/caching divergence for Integer.valueOf(42) == Integer.valueOf(42) (true in Java because of the cache; KeY models value semantics only). Seed the corpus described in Task 2 with these wrapper cases (value, null/NPE, NaN, identity-divergence) and their expected outputs.

- [ ] **Step 7: Format and commit**

    ./gradlew spotlessApply
    git add key.core/src/main/resources/de/uka/ilkd/key/java/JavaRedux key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingWrapperModelTest.java key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus
    git commit -m "feat(java): complete the boxed wrapper models"

---

### Task 2: Semantic corpus and Java-vs-KeY cross-check harness

**Files:**
- Create: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus/cases.tsv
- Create: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus/<case>/<Case>.java
- Create: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus/<case>/expected.txt
- Create: script/autoboxing/check_java_semantics.sh
- Create: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingSemanticsTest.java

**Interfaces:**
- Produces: a corpus layout and two runners. cases.tsv rows are "<case-id> TAB <kind> TAB <class> TAB <contract-method>", where kind is PROVABLE or SPLIT. The Java runner compiles and executes each case with javac/java 21 and diffs stdout against expected.txt (THROWS <exception> is also supported). AutoboxingSemanticsTest loads the same case and checks the recorded KeY verdict.

- [ ] **Step 1: Define the corpus format and seed cases**

Each case directory contains one .java file that is both valid Java 21 (JML comments are ignored by javac) and loadable by KeY. Give it a main method that prints deterministic key=value lines, and (for the KeY side) a contract on the method named in cases.tsv. expected.txt holds the exact stdout or the line THROWS java.lang.NullPointerException. Seed the corpus with the explicit wrapper cases from Task 1:

    explicit-int    PROVABLE
    explicit-long   PROVABLE
    explicit-null   SPLIT

The implicit-conversion cases (uniform-int, null-int, int-promotion) are added in Task 3, once the transformer exists.

- [ ] **Step 2: Write the Java runner**

Create script/autoboxing/check_java_semantics.sh. For every row of cases.tsv it compiles the case with javac --release 21 into a temp directory, runs it with java, and compares stdout to expected.txt. A THROWS <exception> expectation passes only when the process exits non-zero and the stack trace names that exception. Print a per-case PASS/FAIL summary and exit non-zero on any mismatch.

- [ ] **Step 3: Write the KeY runner test**

Create AutoboxingSemanticsTest reading the same cases.tsv from the test classpath. For each case, load the .java file with KeYEnvironment, select the contract by the recorded class and method name, run ProofStarter, and assert: PROVABLE -> proof.closed(); SPLIT -> not closed and one open goal is the null obligation (sequent mentions the null literal).

- [ ] **Step 4: Prove the runner detects wrong expectations**

Temporarily corrupt one expected.txt, run script/autoboxing/check_java_semantics.sh, and confirm it fails with a clear diff; restore the file. Commit the script and corpus only after this check.

- [ ] **Step 5: Run both runners on the seeded corpus**

Run: ./script/autoboxing/check_java_semantics.sh
Run: ./gradlew :key.core:test --tests "de.uka.ilkd.key.java.AutoboxingSemanticsTest" --console=plain

Expected: both PASS; PROVABLE cases agree, SPLIT cases show the null obligation in both worlds, DIVERGENCE cases are documented.

- [ ] **Step 6: Format and commit**

    ./gradlew spotlessApply
    git add script/autoboxing key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingSemanticsTest.java
    git commit -m "test(java): add a Java-vs-KeY autoboxing semantics corpus"

---

### Task 3: Transformer skeleton and assignment contexts

**Files:**
- Create: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/WrapperType.java
- Create: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformer.java
- Create: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java
- Modify: key.core/src/main/java/de/uka/ilkd/key/java/transformations/KeYJavaPipeline.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java

**Interfaces:**
- Produces: AutoboxingTransformer implements JavaTransformer; WrapperType with static WrapperType forPrimitive(String) and forWrapper(String), String primitiveName(), String wrapperName(), String valueOfName(), String valueFieldName(), static boolean isWidening(String from, String to); AutoboxingRewriter.rewrite(TypeDeclaration<?>).

- [ ] **Step 1: Write the failing transformer test**

Create AutoboxingTransformerTest with a helper String rewrite(String source) that parses with JavaParser (LanguageLevel.RAW, JavaSymbolSolver over a CombinedTypeSolver containing a ReflectionTypeSolver for the JDK), applies AutoboxingTransformer, and prints the result. Cases:

    Integer a = 42;                // -> Integer.valueOf(42)
    int i = a;                     // -> int i = a.value;
    Long l = 1L;                   // -> Long.valueOf(1L)
    long v = integerObj;           // -> (long) integerObj.value
    Integer f; void m(){ f = 7; }  // field assignment boxes
    Integer m(){ return 42; }      // return boxes
    static final Integer X = 42;   // field initializer boxes

Assertions use contains/doesNotContain on the printed source.

- [ ] **Step 2: Run it to verify it fails**

Run: ./gradlew :key.core:test --tests "de.uka.ilkd.key.java.AutoboxingTransformerTest" --console=plain

Expected: FAIL (AutoboxingTransformer does not exist).

- [ ] **Step 3: Implement WrapperType and the rewriter**

Implement the wrapper/primitive mapping and the primitive widening order (byte < short < int < long < float < double, plus char). Implement AutoboxingRewriter as a top-down visitor that supplies the expected type for variable declarators (declared type), assignments (target type), return statements (enclosing method return type) and field declarations. Boxing produces a MethodCallExpr on a NameExpr for the wrapper; unboxing produces a FieldAccessExpr named value; widening inserts a CastExpr. Copy the original node's range to synthetic nodes so positions stay meaningful.

- [ ] **Step 4: Register the transformation**

In KeYJavaPipeline.createDefault add p.add(new AutoboxingTransformer()); immediately after RecordClassBuilder and before JMLTransformer, so later builders that clone field initializers see the converted form. In AutoboxingTransformer skip nodes inside com.github.javaparser.ast.jml.* subtrees.

- [ ] **Step 5: Write the failing proof tests for assignment contexts**

In AutoboxingProofTest add:

    Integer a = 42;
    int i = a;
    //@ assert i == 42;

    Integer f;
    void m() { f = 42; int i = f; //@ assert i == 42; }

    Integer m() { return 42; }
    // caller: int i = m(); //@ assert i == 42;

and the null split test:

    /*@ normal_behavior requires true; ensures true; @*/
    public static void m() {
        Integer a = null;
        int i = a;
    }

with the choice runtimeExceptions = runtimeExceptions:ban. Assert that the proof does not close and that one open goal is the null branch (its sequent contains a and null, and no normal-path goal remains).

- [ ] **Step 6: Run the proof tests to verify they fail, then pass**

Run: ./gradlew :key.core:test --tests "de.uka.ilkd.key.java.AutoboxingProofTest" --console=plain

Expected first: the positive cases fail with the sort-mismatch crash; after the implementation: PASS.

- [ ] **Step 7: Extend the corpus and cross-check Java vs KeY**

Add the assignment-context cases (uniform-int, null-int, field, return, initializer) to the corpus with expected.txt files. Run ./script/autoboxing/check_java_semantics.sh and ./gradlew :key.core:test --tests "de.uka.ilkd.key.java.AutoboxingSemanticsTest" --console=plain. Expected: both PASS and the verdicts agree.

- [ ] **Step 8: Format and commit**

    ./gradlew spotlessApply
    git add key.core/src/main/java/de/uka/ilkd/key/java/transformations key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing
    git commit -m "feat(java): desugar boxing and unboxing in assignment contexts"

---

### Task 4: Invocation contexts and varargs

**Files:**
- Modify: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java
- Test: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus

**Interfaces:**
- Consumes: WrapperType and convert(Expression, Target) from Task 3.
- Produces: argument rewriting through ResolvedMethodDeclaration/ResolvedConstructorDeclaration parameter types, including varargs.

- [ ] **Step 1: Add failing tests**

AST:

    static int f(int x); ... int i = f(integerObj);        // -> f(integerObj.value)
    static void g(Integer x); ... g(42);                    // -> g(Integer.valueOf(42))
    static void h(Integer... xs); ... h(1, 2);              // -> h(Integer.valueOf(1), Integer.valueOf(2))
    static void k(int... xs); ... k(integerObj, 2);         // -> k(integerObj.value, 2)

Proof: g(42) called with an int argument does not crash; f(integerObj) proves with a non-null argument; varargs both ways.

- [ ] **Step 2: Run to verify failure, implement, run to pass**

Resolve MethodCallExpr, ObjectCreationExpr and ExplicitConstructorInvocationStmt; get each parameter's ResolvedType; for a varargs array parameter use the component type for the extra arguments. Rewrite each argument with the corresponding Target.

Run: ./gradlew :key.core:test --tests "de.uka.ilkd.key.java.AutoboxingTransformerTest" --tests "de.uka.ilkd.key.java.AutoboxingProofTest" --console=plain

Expected: PASS.

- [ ] **Step 3: Extend the corpus and cross-check Java vs KeY**

Add invocation cases (plain argument, varargs fixed and variable arity, constructor) with expected.txt. Run ./script/autoboxing/check_java_semantics.sh and the AutoboxingSemanticsTest. Expected: both PASS.

- [ ] **Step 4: Format and commit**

    ./gradlew spotlessApply
    git add key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing
    git commit -m "feat(java): box and unbox method and constructor arguments"

---

### Task 5: Numeric promotion

**Files:**
- Modify: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java
- Test: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus

- [ ] **Step 1: Add failing tests**

    Integer a = 42; int i = a + 1;            // -> a.value + 1
    Long l = 1L; long v = l + 1;              // -> l.value + 1
    Integer a; Integer b; boolean r = a == b; // unchanged (reference equality)
    Integer a; boolean r = a == 42;           // -> a.value == 42
    Integer a; long v = a << 2;               // unbox and promote
    Integer a; int x = arr[a];                // -> arr[a.value]
    Integer a; switch (a) { ... }             // -> switch (a.value)

Proof: Integer a = 42; int i = a + 1; //@ assert i == 43; closes. a == b remains a reference comparison and is not proven true.

- [ ] **Step 2: Implement**

For numeric binary operators unbox boxed operands and insert a widening cast to the promoted type (double over float over long over int). For == and != unbox only if at least one operand is a primitive numeric type. Unbox unary +, -, ~, shift operands, array indexes and switch selectors. Skip String concatenation.

- [ ] **Step 3: Extend the corpus and cross-check Java vs KeY**

Add promotion cases (arithmetic, mixed long, shift, array index, switch) with expected.txt, and assert in the AST test that a boxed == boxed comparison stays a reference comparison (no .value inserted). Run the Java script and the KeY test. Expected: both PASS.

- [ ] **Step 4: Format and commit**

    ./gradlew spotlessApply
    git add key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing
    git commit -m "feat(java): apply numeric promotion to boxed operands"

---

### Task 6: Compound assignment, increment and decrement

**Files:**
- Modify: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java
- Test: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus

- [ ] **Step 1: Add failing tests**

    Integer a = 42; a += 1;          // a = Integer.valueOf((int)(a.value + 1))
    Integer a = 42; a++;             // temp = a.value; a = Integer.valueOf(temp + 1)
    Integer a = 42; int i = a++;     // i == 42, a.value == 43
    Integer a = 42; int i = ++a;     // i == 43
    f(a++);                          // evaluation order preserved
    int i = a++ + a++;               // 42 + 43

- [ ] **Step 2: Implement**

Compound assignment: rewrite to a = Wrapper.valueOf((prim) (a.value op rhs)). Increment/decrement: rewrite the nearest enclosing statement into a block. Postfix saves a.value into a fresh temp before the store; prefix reads after the store. When the increment is nested among other side-effecting subexpressions, linearise the expression in Java evaluation order so each subexpression is evaluated once and in order. Use fresh names from the pipeline's naming utility.

- [ ] **Step 3: Extend the corpus and cross-check Java vs KeY**

Add compound-assignment, postfix and prefix cases, including f(a++) and a++ + a++ (DIVERGENCE is not needed; these must agree). Run the Java script and the KeY test. Expected: both PASS.

- [ ] **Step 4: Format and commit**

    ./gradlew spotlessApply
    git add key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing
    git commit -m "feat(java): handle boxed compound assignment and increment"

---

### Task 7: Casts and conditional expressions

**Files:**
- Modify: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java
- Test: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus

- [ ] **Step 1: Add failing tests**

    Integer a = (Integer) 42;       // -> Integer.valueOf(42)
    int i = (int) integerObj;       // -> integerObj.value
    Object o = (Object) 42;         // -> (Object) Integer.valueOf(42)
    int i = flag ? integerObj : 0;  // numeric conditional, unbox
    Integer a = flag ? 1 : 2;       // box the numeric result

- [ ] **Step 2: Implement**

CastExpr: unbox when the target is primitive and the operand is a wrapper; box when the target is a wrapper or a reference supertype and the operand is primitive (add the reference cast when the target is not exactly the wrapper). ConditionalExpr: classify per JLS 15.25 (boolean, numeric, reference), unbox and widen the numeric case, and box primitive branches against the conditional's resolved type.

- [ ] **Step 3: Extend the corpus and cross-check Java vs KeY**

Add cast and conditional cases with expected.txt. Run the Java script and the KeY test. Expected: both PASS.

- [ ] **Step 4: Format and commit**

    ./gradlew spotlessApply
    git add key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing
    git commit -m "feat(java): box and unbox casts and conditionals"

---

### Task 8: Arrays and enhanced for

**Files:**
- Modify: key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java
- Test: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java
- Test: key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing/corpus

- [ ] **Step 1: Add failing tests**

    Integer[] xs = {1, 2};                      // -> {Integer.valueOf(1), Integer.valueOf(2)}
    Integer[] xs = new Integer[2]; xs[0] = 1;   // store boxes
    int i = integerArray[0];                     // unchanged
    int i = xs[0];                               // -> xs[0].value
    for (Integer x : intArray) { }               // box each element
    for (int x : integerArray) { }               // unbox each element

- [ ] **Step 2: Implement**

ArrayInitializerExpr takes the component type from the enclosing array creation or variable declaration. ArrayAccessExpr stores use the array component type; index expressions are unboxed by the numeric-promotion pass. ForEachStmt compares the loop variable's declared type with the element type of the array or Iterable and inserts the conversion at the loop-variable assignment.

- [ ] **Step 3: Extend the corpus and cross-check Java vs KeY**

Add array-initializer, array-store, array-read and both enhanced-for cases with expected.txt. Run the Java script and the KeY test. Expected: both PASS.

- [ ] **Step 4: Format and commit**

    ./gradlew spotlessApply
    git add key.core/src/main/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingRewriter.java key.core/src/test/java/de/uka/ilkd/key/java/transformations/pipeline/AutoboxingTransformerTest.java key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing
    git commit -m "feat(java): box and unbox array elements and enhanced for"

---

### Task 9: Full matrix, documentation and verification

**Files:**
- Modify: key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java
- Modify: key.core/src/test/resources/de/uka/ilkd/key/java/coverage/README.md
- Modify: key.core/src/test/resources/de/uka/ilkd/key/java/coverage/supported/autoboxing/AutoBox.java (only if needed)

- [ ] **Step 1: Add the wrapper matrix**

Parameterise the assignment/proof tests over all eight wrappers (literal, boxing, unboxing, promotion, method argument) so every wrapper is exercised.

- [ ] **Step 2: Update the coverage documentation**

Change the README note that autoboxing "loads but is not soundly modelled": it is now supported for the contexts in the spec. Keep the note about the JML-expression and string-concatenation exclusions.

- [ ] **Step 3: Run the full cross-check and targeted suites**

    ./script/autoboxing/check_java_semantics.sh
    ./gradlew :key.core:test --tests "de.uka.ilkd.key.java.Autoboxing*" --tests "de.uka.ilkd.key.java.JavaFeatureCoverageTest" --console=plain

Expected: PASS; every corpus case agrees between Java and KeY.

- [ ] **Step 4: Format and nullness**

    ./gradlew spotlessCheck
    ./gradlew -DENABLE_NULLNESS=true :key.core:compileTestJava

Expected: both succeed.

- [ ] **Step 5: Commit and report**

    git add key.core/src/test/java/de/uka/ilkd/key/java/AutoboxingProofTest.java key.core/src/test/resources/de/uka/ilkd/key/java/coverage key.core/src/test/resources/de/uka/ilkd/key/java/autoboxing
    git commit -m "test(java): cover autoboxing across wrappers and update coverage docs"

Report the branch, the head, the Java-vs-KeY corpus results, and any remaining limitation. Do not push and do not open a PR unless the user asks.
