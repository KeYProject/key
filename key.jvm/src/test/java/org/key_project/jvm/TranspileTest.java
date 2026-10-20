/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.regex.Pattern;
import javax.tools.ToolProvider;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * M1 transpiler fidelity gate: compiles the {@code fixtures/Max.java} source, transpiles the
 * resulting bytecode with {@link Transpiler}, checks the <em>canonical linear layout</em> of the
 * emitted Java (plain-Java locals, {@code stk.push(...)}/pop-style stack effects on a single
 * {@code jvm.Local} frame, int-target {@code jvm.Local.goto_(...)} calls, guarded label blocks,
 * mid-layout return wrapper), and round-trips the emitted sources through {@code javac}.
 * <p>
 * The shape asserted here mirrors {@code golden/Max.java}, against which the closing proof tests
 * run (the golden twin carries the JML contracts ASM cannot retain).
 */
class TranspileTest {

    @TempDir
    Path tmpDir;

    @Test
    void transpiledOutputHasCanonicalLayoutAndCompiles() throws Exception {
        Path src = writeFixture("Max.java");
        Path classes = tmpDir.resolve("classes");

        compile(src.resolve("fixtures").resolve("Max.java"), classes);
        Assumptions.assumeTrue(Files.exists(classes.resolve("Max.class")),
            "fixture compile produced no class file (javac unavailable?)");

        Path out = tmpDir.resolve("out");
        List<Path> emitted = Transpiler.transpile(List.of(classes.resolve("Max.class")), out);

        assertThat(emitted).singleElement().satisfies(this::assertCanonicalLayout);

        // javac round-trip of the transpiled output (including the copied runtime).
        Path roundTripClasses = tmpDir.resolve("roundtrip");
        int rc =
            compile(emitted.get(0), out.resolve("jvm").resolve("Local.java"), roundTripClasses);
        assertThat(rc).as("javac must compile the transpiled output").isZero();
    }

    /**
     * The recursive self-call: popping the argument into a temp and pushing the result of the
     * <em>self-call</em> must be a real {@code stk.push(fact($v0))} (operation-contract
     * application points at the method itself), inside the guarded label block of the forward
     * {@code goto_}. The proof side of this shape is covered by {@link RecursionProofTest}.
     */
    @Test
    void transpiledRecursiveSelfCallHasCanonicalShape() throws Exception {
        Path src = writeFixture("Fact.java");
        Path classes = tmpDir.resolve("classes-fact");

        compile(src.resolve("fixtures").resolve("Fact.java"), classes);
        Assumptions.assumeTrue(Files.exists(classes.resolve("Fact.class")),
            "fixture compile produced no class file (javac unavailable?)");

        Path out = tmpDir.resolve("out-fact");
        List<Path> emitted = Transpiler.transpile(List.of(classes.resolve("Fact.class")), out);

        Path factJava = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Fact.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Fact.java emitted"));
        String s = Files.readString(factJava, StandardCharsets.UTF_8);

        // argument popped into a temp, then the real self-call pushed onto the stack
        assertThat(s).contains("int $v0 = stk.pop();").contains("stk.push(fact($v0));")
                .contains("stk.imul();").contains("return stk.top();");

        // conditional forward jump into the guarded label block around the recursion
        assertThat(
            Pattern.compile("if \\(stk\\.if_icmpgt\\(\\)\\) \\{ jvm\\.Local\\.goto_\\(\\d+\\); \\}")
                    .matcher(s).find())
                .isTrue();
        assertThat(Pattern.compile("L\\d+: \\{ if \\(false\\) \\{ break L\\d+; \\}").matcher(s)
                .find()).isTrue();

        Path roundTripClasses = tmpDir.resolve("roundtrip-fact");
        int rc = compile(factJava, out.resolve("jvm").resolve("Local.java"), roundTripClasses);
        assertThat(rc).as("javac must compile the transpiled recursive output").isZero();
    }

    /**
     * M2 object slice: the emitted code for allocations, fields and instance calls must have the
     * canonical shape (real Java fields, fused {@code new+init}, instance calls on the receiver
     * expression without any class qualifier) and round-trip through {@code javac}. The golden
     * twins of this shape live in {@code golden/Point.java} + {@code golden/Shapes.java}
     * (carrying the JML contracts ASM cannot retain); the proof-side characterization of these
     * fixtures is {@code rule.ObjectProofTest}.
     */
    @Test
    void transpiledObjectCodeHasCanonicalLayoutAndCompiles() throws Exception {
        Path src = writeFixture("Point.java");
        writeFixture("Shapes.java");
        Path classes = tmpDir.resolve("classes-object");

        int rcFix = compile(
            List.of(src.resolve("fixtures").resolve("Point.java"),
                src.resolve("fixtures").resolve("Shapes.java")),
            classes);
        Assumptions.assumeTrue(rcFix == 0 && Files.exists(classes.resolve("Point.class"))
                && Files.exists(classes.resolve("Shapes.class")),
            "fixture compile failed (rc=" + rcFix + "); javac unavailable?");

        Path out = tmpDir.resolve("out-object");
        List<Path> emitted = Transpiler.transpile(
            List.of(classes.resolve("Point.class"), classes.resolve("Shapes.class")), out);

        Path pointJava =
            emitted.stream().filter(p -> p.getFileName().toString().equals("Point.java"))
                    .findFirst().orElseThrow(() -> new AssertionError("no Point.java emitted"));
        Path shapesJava =
            emitted.stream().filter(p -> p.getFileName().toString().equals("Shapes.java"))
                    .findFirst().orElseThrow(() -> new AssertionError("no Shapes.java emitted"));

        // real Java fields, explicit ctor, super-<init> dropped (implicit in Java)
        String p = Files.readString(pointJava, StandardCharsets.UTF_8);
        assertThat(p).contains("public int x;").contains("public int y;")
                .contains("public Point(int a, int b) {")
                // field accesses are real Java on the receiver popped off the reference stack
                .contains("$o1.x = $v0;").contains("$o3.y = $v2;")
                .contains("stk.push($o0.x);").contains("stk.iadd();")
                // the Object.<init> super call in the ctor is dropped; receiver popped
                .containsPattern("stk\\.push\\(this\\);\n        stk\\.popRef\\(\\);")
                .doesNotContain("Object.<init>");

        // new+dup+invokespecial<init> fused; args popped before the constructor call
        String s = Files.readString(shapesJava, StandardCharsets.UTF_8);
        assertThat(s).contains("Point $t2 = new Point($c1, $c0);").contains("stk.push($t2);")
                // astore/aload of a reference local through the stack
                .contains("local_0 = (Point) stk.popRef();").contains("stk.push(local_0);")
                // instance call on the receiver, no class qualifier
                .contains("stk.push($o3.sum());").doesNotContain(".Point.sum")
                // field reads through the reference stack with the typed cast
                .contains("stk.push($o0.x);");

        // javac round-trip of both emitted classes together with the copied runtime.
        Path roundTripClasses = tmpDir.resolve("roundtrip-object");
        int rc = compile(
            List.of(pointJava, shapesJava, out.resolve("jvm").resolve("Local.java")),
            roundTripClasses);
        assertThat(rc).as("javac must compile the transpiled object output").isZero();
    }

    /**
     * M2 static-field slice: getstatic/putstatic read and write the real Java static field
     * around int pops / typed reference popRefs; the emitted code round-trips through javac.
     * The golden twin of this shape is {@code golden/Counter.java}; no closing proof gate exists
     * (Object-typed ops, see {@code rule.ObjectProofTest} and docs §9.1(2)).
     */
    @Test
    void transpiledStaticFieldAccessHasCanonicalShape() throws Exception {
        Path src = writeFixture("Point.java");
        writeFixture("Counter.java");
        Path classes = tmpDir.resolve("classes-static");

        int rcFix = compile(
            List.of(src.resolve("fixtures").resolve("Point.java"),
                src.resolve("fixtures").resolve("Counter.java")),
            classes);
        Assumptions.assumeTrue(rcFix == 0 && Files.exists(classes.resolve("Counter.class"))
                && Files.exists(classes.resolve("Point.class")),
            "fixture compile failed (rc=" + rcFix + "); javac unavailable?");

        Path out = tmpDir.resolve("out-static");
        List<Path> emitted = Transpiler.transpile(
            List.of(classes.resolve("Counter.class"), classes.resolve("Point.class")), out);

        Path counterJava = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Counter.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Counter.java emitted"));
        String s = Files.readString(counterJava, StandardCharsets.UTF_8);

        // int static field: getstatic pushes the real field, putstatic pops into a temp
        assertThat(s).contains("stk.push(Counter.calls);").contains("int $v0 = stk.pop();")
                .contains("Counter.calls = $v0;").contains("return stk.top();");

        // reference static field: getstatic pushes the real field (Object overload), areturn
        // casts topRef to the declared return type
        assertThat(s).contains("stk.push(Counter.mark);").contains("return (Point) stk.topRef();");

        // void method header is spelled correctly (void-returning methods have no return slot)
        assertThat(s).contains("public static void remember(Point p) {")
                .doesNotContain("voidremember");

        // javac round-trip of both emitted classes with the runtime
        Path roundTripClasses = tmpDir.resolve("roundtrip-static");
        int rc = compile(List.of(counterJava, emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Point.java")).findFirst()
                .orElseThrow(),
            out.resolve("jvm").resolve("Local.java")), roundTripClasses);
        assertThat(rc).as("javac must compile the transpiled static-field output").isZero();
    }

    /**
     * M2 cast slice: checkcast pops and re-pushes the real cast (Point), instanceof pops and
     * pushes the JVM int 0/1 result as a real instanceof expression; the classify method also
     * exercises the constrained-goto mid-layout return wrapper. javac round-trip must compile.
     * The golden twin of this shape is {@code golden/Caster.java}; no closing proof gate exists
     * (Object-typed ops, see {@code rule.ObjectProofTest} and docs §9.1(2)).
     */
    @Test
    void transpiledCastAndInstanceofHaveCanonicalShape() throws Exception {
        Path src = writeFixture("Point.java");
        writeFixture("Caster.java");
        Path classes = tmpDir.resolve("classes-caster");
        int rcFix = compile(
            List.of(src.resolve("fixtures").resolve("Point.java"),
                src.resolve("fixtures").resolve("Caster.java")),
            classes);
        Assumptions.assumeTrue(rcFix == 0 && Files.exists(classes.resolve("Caster.class"))
                && Files.exists(classes.resolve("Point.class")),
            "fixture compile failed (rc=" + rcFix + "); javac unavailable?");

        Path out = tmpDir.resolve("out-caster");
        List<Path> emitted = Transpiler.transpile(
            List.of(classes.resolve("Caster.class"), classes.resolve("Point.class")), out);
        Path casterJava = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Caster.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Caster.java emitted"));
        String s = Files.readString(casterJava, StandardCharsets.UTF_8);

        // checkcast: pops a reference, performs the real cast, pushes the typed reference back
        assertThat(s).contains("Point $o0 = (Point) stk.popRef();").contains("stk.push($o0);")
                .contains("return (Point) stk.topRef();");

        // instanceof: pops the reference, pushes the int result of the real instanceof
        assertThat(s).contains("Object $o0 = (Object) stk.popRef();")
                .contains("stk.push($o0 instanceof Point ? 1 : 0);");

        // the instanceof branch is consumed by a constrained goto (mid-layout return wrapper)
        assertThat(s).contains("if (stk.ifeq()) { jvm.Local.goto_(9); }")
                .contains("if (true) { return stk.top(); }");

        int rc = compile(List.of(casterJava, emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Point.java")).findFirst()
                .orElseThrow(),
            out.resolve("jvm").resolve("Local.java")), tmpDir.resolve("roundtrip-caster"));
        assertThat(rc).as("javac must compile the transpiled cast output").isZero();
    }

    /**
     * M2 arrays slice: newarray pops the length and pushes the real allocation (int[] only),
     * iaload/iastore read and write the real int[], arraylength pushes {@code .length}.
     * javac round-trip must compile. The golden twin of this shape is
     * {@code golden/Arrays.java}; no closing proof gate exists (Object-typed ops, see
     * {@code rule.ObjectProofTest} and docs §9.1(2)).
     */
    @Test
    void transpiledIntArrayOpsHaveCanonicalShape() throws Exception {
        Path src = writeFixture("Arrays.java");
        Path classes = tmpDir.resolve("classes-arrays");
        int rcFix = compile(src.resolve("fixtures").resolve("Arrays.java"), classes);
        Assumptions.assumeTrue(rcFix == 0 && Files.exists(classes.resolve("Arrays.class")),
            "fixture compile failed (rc=" + rcFix + "); javac unavailable?");

        Path out = tmpDir.resolve("out-arrays");
        List<Path> emitted =
            Transpiler.transpile(List.of(classes.resolve("Arrays.class")), out);
        Path arraysJava = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Arrays.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Arrays.java emitted"));
        String s = Files.readString(arraysJava, StandardCharsets.UTF_8);

        // arraylength: pops the array reference, pushes .length
        assertThat(s).contains("int[] $a0 = (int[]) stk.popRef();")
                .contains("stk.push($a0.length);");

        // iaload: index on top, then the array reference
        assertThat(s).contains("int $i0 = stk.pop();").contains("int[] $a1 = (int[]) stk.popRef();")
                .contains("stk.push($a1[$i0]);");

        // iastore: value, index, then the array reference (the real store)
        assertThat(s).contains("int $v0 = stk.pop();").contains("int $i1 = stk.pop();")
                .contains("int[] $a2 = (int[]) stk.popRef();").contains("$a2[$i1] = $v0;");

        // newarray: pops the length, pushes the real allocation; params typed int[]
        assertThat(s).contains("int[] $a0 = new int[stk.pop()];").contains("stk.push($a0);")
                .contains("public static int[] make(int n) {")
                .contains("return (int[]) stk.topRef();");

        int rc = compile(List.of(arraysJava, out.resolve("jvm").resolve("Local.java")),
            tmpDir.resolve("roundtrip-arrays"));
        assertThat(rc).as("javac must compile the transpiled array output").isZero();
    }

    /**
     * M2 stub slice: transpiling a class that references an external (not transpiled) type must
     * emit a stub class carrying exactly the members the output accesses — instance field
     * {@code score} (get/putfield), instance method {@code size()} (invokevirtual), static
     * field {@code kind} (getstatic), static method {@code defaultScore()} (invokestatic) and
     * the no-arg constructor (new+init fusion) — with default-valued bodies so the output
     * compiles. The golden twin of the transpiled class is {@code golden/Guard.java}.
     */
    @Test
    void transpiledExternalTypeReferenceEmitsStub() throws Exception {
        Path src = writeFixture("Gadget.java");
        writeFixture("Guard.java");
        Path classes = tmpDir.resolve("classes-stub");
        int rcFix = compile(
            List.of(src.resolve("fixtures").resolve("Gadget.java"),
                src.resolve("fixtures").resolve("Guard.java")),
            classes);
        Assumptions.assumeTrue(rcFix == 0 && Files.exists(classes.resolve("Guard.class"))
                && Files.exists(classes.resolve("Gadget.class")),
            "fixture compile failed (rc=" + rcFix + "); javac unavailable?");

        // only Guard is transpiled; Gadget is the external type the stub must cover
        Path out = tmpDir.resolve("out-stub");
        List<Path> emitted =
            Transpiler.transpile(List.of(classes.resolve("Guard.class")), out);
        Path stub = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Gadget.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Blueprint stub Gadget.java emitted"));
        String s = Files.readString(stub, StandardCharsets.UTF_8);

        // the stub carries exactly the accessed members with default bodies
        assertThat(s).contains("public class Gadget {").contains("public int score;")
                .contains("public int size() { return 0; }")
                .contains("public static int kind;")
                .contains("public static int defaultScore() { return 0; }")
                .contains("public Gadget() { }");

        // the transpiled Guard compiles against the stub and the runtime
        Path guardJava = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Guard.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Guard.java emitted"));
        int rc = compile(List.of(guardJava, stub, out.resolve("jvm").resolve("Local.java")),
            tmpDir.resolve("roundtrip-stub"));
        assertThat(rc).as("javac must compile the transpiled class against its stubs").isZero();
    }

    /**
     * M3 switch slice: tableswitch/lookupswitch pop the selector into a plain int temp and
     * dispatch as an if-chain of {@code if (sel == key) { jvm.Local.goto_(pc); }} over the dense
     * key range (resp. sparse key list), followed by an unconditional {@code goto_(dflt)}; every
     * case/default becomes a guarded {@code L<pc>} block. javac round-trip must compile. The
     * golden twin of this shape is {@code golden/SwitchClass.java}; the proof side closes (int
     * only) and is gated by {@code rule.SwitchProofTest}.
     */
    @Test
    void transpiledSwitchHasCanonicalShape() throws Exception {
        Path src = writeFixture("SwitchClass.java");
        Path classes = tmpDir.resolve("classes-switch");
        int rcFix = compile(src.resolve("fixtures").resolve("SwitchClass.java"), classes);
        Assumptions.assumeTrue(rcFix == 0 && Files.exists(classes.resolve("SwitchClass.class")),
            "fixture compile failed (rc=" + rcFix + "); javac unavailable?");

        Path out = tmpDir.resolve("out-switch");
        List<Path> emitted =
            Transpiler.transpile(List.of(classes.resolve("SwitchClass.class")), out);
        Path switchJava = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("SwitchClass.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no SwitchClass.java emitted"));
        String s = Files.readString(switchJava, StandardCharsets.UTF_8);

        // tableswitch (dense 0..2): selector temp + if-chain + unconditional default jump
        assertThat(s).contains("int $s0 = stk.pop();")
                .contains("if ($s0 == 0) { jvm.Local.goto_(4); }")
                .contains("if ($s0 == 1) { jvm.Local.goto_(9); }")
                .contains("if ($s0 == 2) { jvm.Local.goto_(9); }")
                .contains("jvm.Local.goto_(14);");

        // lookupswitch (sparse 7/100): only the explicit keys are tested
        assertThat(s).contains("if ($s0 == 7) { jvm.Local.goto_(4); }")
                .contains("if ($s0 == 100) { jvm.Local.goto_(9); }");

        // case bodies: guarded label blocks with mid-layout / trailing returns
        assertThat(s).contains("L4: { if (false) { break L4; }").contains("stk.push(10);")
                .contains("if (true) { return stk.top(); }").contains("stk.push(-1);");

        int rc = compile(List.of(switchJava, out.resolve("jvm").resolve("Local.java")),
            tmpDir.resolve("roundtrip-switch"));
        assertThat(rc).as("javac must compile the transpiled switch output").isZero();
    }

    /**
     * M3 stack-shuffle slice: the runtime rearrangement calls the transpiler emits for
     * javac-17's real bytecode — {@code stk.dup();} for {@code (x = y) + x} and
     * {@code stk.dup2();} for the int-array compound {@code a[i] += v}. The golden twin is
     * {@code golden/Shuffle.java}; {@code dupReuse} is variable-only int and closes
     * ({@code rule.ShuffleProofTest}), {@code dup2A} carries the §9.1(2) residual.
     */
    @Test
    void transpiledStackShufflesHaveCanonicalShape() throws Exception {
        Path src = writeFixture("Shuffle.java");
        Path classes = tmpDir.resolve("classes-shuffle");
        int rcFix = compile(src.resolve("fixtures").resolve("Shuffle.java"), classes);
        Assumptions.assumeTrue(rcFix == 0 && Files.exists(classes.resolve("Shuffle.class")),
            "fixture compile failed (rc=" + rcFix + "); javac unavailable?");

        Path out = tmpDir.resolve("out-shuffle");
        List<Path> emitted =
            Transpiler.transpile(List.of(classes.resolve("Shuffle.class")), out);
        Path shuffleJava = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Shuffle.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Shuffle.java emitted"));
        String s = Files.readString(shuffleJava, StandardCharsets.UTF_8);

        // (x = y) + x: push(y); dup; pop into x; re-push; iadd -- all int
        assertThat(s).contains("stk.push(y);").contains("stk.dup();")
                .contains("x = stk.pop();").contains("stk.push(x);")
                .contains("stk.iadd();");
        // a[i] += v: dup2 of array base + index before the load/store pair
        assertThat(s).contains("stk.push(a);").contains("stk.push(i);")
                .contains("stk.dup2();");
        // no constant leaked into the stack machine of dupReuse (variable-only)
        assertThat(s).doesNotContain("stk.push(0);").doesNotContain("stk.push(1);");

        int rc = compile(List.of(shuffleJava, out.resolve("jvm").resolve("Local.java")),
            tmpDir.resolve("roundtrip-shuffle"));
        assertThat(rc).as("javac must compile the transpiled shuffle output").isZero();
    }

    /**
     * M3 category-2 slice: long/double/float stack ops, conversions, lcmp and long arrays as
     * emitted for javac-17's real bytecode. The golden twin is {@code golden/Category2.java};
     * {@code back} ({@code l2i}) and {@code flt} (pure float) close
     * ({@code rule.Category2ProofTest}), the long-arithmetic and literal-carrying flows are
     * pinned per §9.1(2). JVM booleans are pushed as int 0/1 — never boxed into
     * {@code push(Object)}.
     */
    @Test
    void transpiledCategory2OpsHaveCanonicalShape() throws Exception {
        Path src = writeFixture("Category2.java");
        Path classes = tmpDir.resolve("classes-cat2");
        int rcFix = compile(src.resolve("fixtures").resolve("Category2.java"), classes);
        Assumptions.assumeTrue(rcFix == 0 && Files.exists(classes.resolve("Category2.class")),
            "fixture compile failed (rc=" + rcFix + "); javac unavailable?");

        Path out = tmpDir.resolve("out-cat2");
        List<Path> emitted =
            Transpiler.transpile(List.of(classes.resolve("Category2.class")), out);
        Path cat2 = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Category2.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Category2.java emitted"));
        String s = Files.readString(cat2, StandardCharsets.UTF_8);

        // long arithmetic + constants (ldc2_w)
        assertThat(s).contains("stk.pushL(a);").contains("stk.pushL(b);")
                .contains("stk.ladd();").contains("return stk.topL();")
                .contains("stk.pushL(42L);");
        // lcmp feeding the sign branch; conversions i2l / l2i
        assertThat(s).contains("stk.lcmp();").contains("if (stk.ifge())");
        assertThat(s).contains("stk.i2l();").contains("stk.l2i();");
        // doubles + floats (+ldc2_w literals, i2d)
        assertThat(s).contains("stk.pushD(a);").contains("stk.pushD(2.0);")
                .contains("stk.dmul();").contains("return stk.topD();")
                .contains("stk.i2d();").contains("stk.pushD(0.5);")
                .contains("stk.pushF(a);").contains("stk.pushF(b);")
                .contains("stk.fmul();").contains("return stk.topF();");
        // boolean selector: int 0/1, never boxed
        assertThat(s).contains("stk.push((c ? 1 : 0));").doesNotContain("stk.push(c);");
        // long-array compound: dup2 of base+index, laload/lastore
        assertThat(s).contains("stk.dup2();").contains("long[] $a1 = (long[]) stk.popRef();")
                .contains("stk.pushL($a1[$i0]);").contains("long $v2 = stk.popL();");

        int rc = compile(List.of(cat2, out.resolve("jvm").resolve("Local.java")),
            tmpDir.resolve("roundtrip-cat2"));
        assertThat(rc).as("javac must compile the transpiled category-2 output").isZero();
    }

    /**
     * M3 exceptions slice: javac-17's real try/catch bytecode must come out as structured Java
     * {@code try/catch} blocks recovered from the exception table, not linear handler code. The
     * try range {@code [start,end)} of the table becomes {@code try { }}, each handler is
     * consumed into a real catch clause (its leading {@code astore} binds the catch variable
     * {@code local_<slot>} instead of declaring a local), the finally-inlined catch-all handler
     * rethrows the bound exception, and {@code athrow} becomes a real
     * {@code throw (Throwable) ...} (hence {@code throws Throwable} on methods that may throw).
     * {@code LDC} of a {@code String} is a plain push. Golden twin:
     * {@code golden/Exceptions.java}; proof characterization {@code rule.ExceptionsProofTest}.
     */
    @Test
    void transpiledExceptionsHaveCanonicalShape() throws Exception {
        Path src = writeFixture("Exceptions.java");
        Path classes = tmpDir.resolve("classes-exc");
        int rcFix = compile(src.resolve("fixtures").resolve("Exceptions.java"), classes);
        Assumptions.assumeTrue(rcFix == 0 && Files.exists(classes.resolve("Exceptions.class")),
            "fixture compile failed (rc=" + rcFix + "); javac unavailable?");

        Path out = tmpDir.resolve("out-exc");
        List<Path> emitted =
            Transpiler.transpile(List.of(classes.resolve("Exceptions.class")), out);
        Path exc = emitted.stream()
                .filter(p -> p.getFileName().toString().equals("Exceptions.java")).findFirst()
                .orElseThrow(() -> new AssertionError("no Exceptions.java emitted"));
        String s = Files.readString(exc, StandardCharsets.UTF_8);

        // structured try/catch from the exception table; handler entry binds the catch var
        assertThat(s).contains("        try {")
                .contains("} catch (IllegalArgumentException local_1) {")
                .contains("} catch (Throwable local_2) {");
        // the athrow is a real throw; methods that may throw declare it
        assertThat(s).contains("throws Throwable")
                .contains("if (true) { throw (Throwable) stk.popRef(); }");
        // the finally-inlined catch-all rethrows the bound exception variable
        assertThat(s).contains("stk.push(local_2);");
        // LDC String + new+<init> fusion with a String argument
        assertThat(s).contains("stk.push(\"boom\");")
                .contains("String $c0 = (String) stk.popRef();")
                .contains("IllegalArgumentException $t1 = new IllegalArgumentException($c0);");
        // the handler instructions are not linearly emitted (the catch consumes them)
        assertThat(s).doesNotContain("stk.popRef();\n        stk.push(x);");

        int rc = compile(List.of(exc, out.resolve("jvm").resolve("Local.java")),
            tmpDir.resolve("roundtrip-exc"));
        assertThat(rc).as("javac must compile the transpiled exceptions output").isZero();
    }

    // -- helpers -----------------------------------------------------------------

    private Path writeFixture() throws IOException {
        return writeFixture("Max.java");
    }

    private Path writeFixture(String name) throws IOException {
        Path src = tmpDir.resolve("src");
        Path fixtures = src.resolve("fixtures");
        Files.createDirectories(fixtures);
        try (InputStream in = getClass().getResourceAsStream("/fixtures/" + name)) {
            Files.copy(in, fixtures.resolve(name));
        }
        return src;
    }

    private int compile(Path javaFile, Path classesDir) throws IOException {
        return compile(javaFile, null, classesDir);
    }

    private int compile(Path javaFile, Path localRuntime, Path classesDir) throws IOException {
        var compiler = ToolProvider.getSystemJavaCompiler();
        Assumptions.assumeTrue(compiler != null, "no system javac available; skipping round-trip");
        Files.createDirectories(classesDir);
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        if (localRuntime != null) {
            return compiler.run(null, null, err, "-d", classesDir.toString(), "--release", "17",
                "-g", javaFile.toString(), localRuntime.toString());
        }
        return compiler.run(null, null, err, "-d", classesDir.toString(), "--release", "17", "-g",
            javaFile.toString());
    }

    private int compile(List<Path> sources, Path classesDir) throws IOException {
        var compiler = ToolProvider.getSystemJavaCompiler();
        Assumptions.assumeTrue(compiler != null, "no system javac available; skipping round-trip");
        Files.createDirectories(classesDir);
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        String[] args = new String[sources.size() + 5];
        args[0] = "-d";
        args[1] = classesDir.toString();
        args[2] = "--release";
        args[3] = "17";
        args[4] = "-g";
        for (int i = 0; i < sources.size(); i++) {
            args[i + 5] = sources.get(i).toString();
        }
        return compiler.run(null, null, err, args);
    }

    private void assertCanonicalLayout(Path emitted) throws IOException {
        String s = Files.readString(emitted, StandardCharsets.UTF_8);

        // one runtime frame object, created up front (no static EMPTY: static init is disabled
        // in the proofs, so an EMPTY field read would be null)
        assertThat(s).contains("jvm.Local stk = new jvm.Local();");
        assertThat(s).doesNotContain("jvm.Local.EMPTY");

        // locals/parameters are plain Java: no JVM-slot addressing through the runtime at all
        assertThat(s).doesNotContain("setLocalInt").doesNotContain("setLocalRef");
        assertThat(s).doesNotContain(".iload(").doesNotContain(".istore(")
                .doesNotContain("pushInt");

        // operand stack effects are calls on the one stack frame
        assertThat(s).contains("stk.push(0);");
        assertThat(s).matches("(?s).*local_2 = stk\\.pop\\(\\).*");
        assertThat(s).doesNotContain("stk = stk.push");

        // conditional forward jump: int-target goto guarded by the icmp result
        assertThat(Pattern
                .compile("if \\(stk\\.if_icmplt\\(\\)\\) \\{ jvm\\.Local\\.goto_\\(\\d+\\); \\}")
                .matcher(s).find()).isTrue();
        // unconditional forward jump (loop back-edges in sum/fact)
        assertThat(Pattern.compile("jvm\\.Local\\.goto_\\(\\d+\\);").matcher(s).find()).isTrue();

        // guarded label blocks (transpiler's canonical layout, one per target)
        assertThat(Pattern.compile("L\\d+: \\{ if \\(false\\) \\{ break L\\d+; \\}").matcher(s)
                .find()).isTrue();

        // mid-layout return wrapper (max2) and dead trailing return for the label layout
        assertThat(s).contains("if (true) { return stk.top(); }");
        assertThat(s).contains("return 0;");

        // no heap/array model remnants, no string-encoded goto targets
        assertThat(s).doesNotContain("goto_(\"L").doesNotContain("ispI").doesNotContain("I[");
    }
}
