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
