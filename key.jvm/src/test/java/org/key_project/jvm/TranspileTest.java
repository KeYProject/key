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
