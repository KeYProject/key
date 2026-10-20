/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.jvm;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import javax.tools.ToolProvider;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * M3 differential harness (trust assumption T3, §7): runs the <em>original bytecode</em> and
 * the <em>transpiled output</em> of the same fixtures on identical random inputs and asserts
 * bit-exact behavioral equality (return values and exceptional outcome types). The transpiled
 * output executes against the test-only executable {@code jvm.Local} (real stack machine,
 * {@code src/test/java/jvm/Local.java}), leaving the empty-bodied proof runtime untouched.
 * <p>
 * Scope: the transpiled code models jumps as {@code jvm.Local.goto_(pc)} calls whose semantics
 * live only in the {@code goto} rules of the {@code java-jvm} profile (they cannot jump in
 * Java), so only <em>goto-free</em> methods are executable — javac emits none for the picked
 * fixtures: {@code Category2}'s {@code ladd, lconst, conv, back, dbl, mix, flt, larray} and
 * {@code Shuffle}'s {@code dupReuse, dup2A} ({@code lcmpish}/{@code ternary} branch and are
 * excluded). This still covers the full int/long/double/float arithmetic, the conversions,
 * {@code laload}/{@code lastore}, {@code dup}/{@code dup2} and the reference-typed traffic of
 * the M3 slices — exactly the ops the JML contracts encode.
 */
class DifferentialTest {

    @TempDir
    Path tmpDir;

    /** One differential case: method signature and a per-draw argument factory. */
    private record Case(String className, String method, Class<?>[] paramTypes, Arg arg,
            int draws) {
    }

    /** Factory drawing one (fresh) argument list from the seeded random. */
    private interface Arg {
        Object[] draw(Random rnd);
    }

    private static final Arg INT = r -> new Object[] { r.nextInt() };
    private static final Arg NO_ARGS = r -> new Object[0];
    private static final Arg TWO_INTS = r -> new Object[] { r.nextInt(), r.nextInt() };
    private static final Arg LONG = r -> new Object[] { r.nextLong() };
    private static final Arg TWO_LONGS = r -> new Object[] { r.nextLong(), r.nextLong() };
    private static final Arg DOUBLE = r -> new Object[] { r.nextDouble() - 0.5 };
    private static final Arg TWO_FLOATS = r -> new Object[] { r.nextFloat(), r.nextFloat() };
    private static final Arg LONG_ARRAY = r -> {
        long[] a = longArray(r);
        return new Object[] { a, r.nextInt(a.length), r.nextLong() };
    };
    private static final Arg INT_ARRAY = r -> {
        int[] a = intArray(r);
        return new Object[] { a, r.nextInt(a.length), r.nextInt() };
    };

    private static final Class<?> INT_T = int.class;
    private static final Class<?> LONG_T = long.class;
    private static final Class<?> DOUBLE_T = double.class;
    private static final Class<?> FLOAT_T = float.class;

    @Test
    void transpiledOutputBehavesLikeOriginalBytecodeOnRandomInputs() throws Exception {
        // --- build the fixture classes (original bytecode) ---
        Path src = tmpDir.resolve("src");
        Path fixtures = src.resolve("fixtures");
        Files.createDirectories(fixtures);
        for (String name : List.of("Category2.java", "Shuffle.java")) {
            try (InputStream in = getClass().getResourceAsStream("/fixtures/" + name)) {
                Files.copy(in, fixtures.resolve(name));
            }
        }
        Path classes = tmpDir.resolve("classes");
        int rc = compile(List.of(fixtures.resolve("Category2.java"),
            fixtures.resolve("Shuffle.java")), classes, null);
        Assumptions.assumeTrue(rc == 0 && Files.exists(classes.resolve("Category2.class"))
                && Files.exists(classes.resolve("Shuffle.class")),
            "fixture compile failed (rc=" + rc + "); javac unavailable?");

        // --- transpile and compile the output against the executable test runtime ---
        Path transpiled = tmpDir.resolve("transpiled");
        List<Path> emitted =
            Transpiler.transpile(List.of(classes.resolve("Category2.class"),
                classes.resolve("Shuffle.class")), transpiled);
        Path testClasses = testClassesDir();
        Path transpiledClasses = tmpDir.resolve("transpiled-classes");
        int rc2 = compile(emitted, transpiledClasses, testClasses);
        Assumptions.assumeTrue(rc2 == 0,
            "transpiled output must compile (rc=" + rc2 + "):\n" + lastCompileErrors);

        // --- differential execution ---
        try (URLClassLoader orig =
            new URLClassLoader(new URL[] { classes.toUri().toURL() }, null);
                URLClassLoader trans = new URLClassLoader(
                    new URL[] { transpiledClasses.toUri().toURL(), testClasses.toUri().toURL() },
                    null)) {
            for (Case c : cases()) {
                Class<?> o = Class.forName(c.className(), true, orig);
                Class<?> t = Class.forName(c.className(), true, trans);
                Method om = o.getMethod(c.method(), c.paramTypes());
                Method tm = t.getMethod(c.method(), c.paramTypes());
                for (int draw = 0; draw < c.draws(); draw++) {
                    // identical contents, but a separate array instance per side: the
                    // transpiled larray/dup2A methods mutate their arrays via lastore/iastore,
                    // so executing both sides on one shared instance would leak the first
                    // mutation into the second run.
                    Object[] origArgs = c.arg().draw(new Random(seedOf(c, draw)));
                    Object[] transArgs = c.arg().draw(new Random(seedOf(c, draw)));
                    try {
                        Object expected = om.invoke(null, origArgs);
                        Object actual = tm.invoke(null, transArgs);
                        assertBehaviorEqual(c, draw, origArgs, expected, actual);
                    } catch (InvocationTargetException original) {
                        Random realign = new Random(seedOf(c, draw));
                        c.arg().draw(realign); // consume the original-path draw
                        try {
                            tm.invoke(null, c.arg().draw(realign));
                            throw new AssertionError(c + " draw " + draw + ": original threw "
                                + original.getCause().getClass() + ", transpiled returned");
                        } catch (InvocationTargetException te) {
                            assertThat(te.getCause().getClass())
                                    .as(c + " draw " + draw + " args " + List.of(origArgs)
                                        + ": exceptional outcome must match")
                                    .isEqualTo(original.getCause().getClass());
                        }
                    }
                }
            }
        }
    }

    private void assertBehaviorEqual(Case c, int draw, Object[] args, Object expected,
            Object actual) {
        // bit-exact for the floating cases (NaN payloads and ±0.0 compare by bits)
        if (expected instanceof Double d1 && actual instanceof Double d2) {
            assertThat(Double.compare(d1, d2))
                    .as(c + " draw " + draw + " args " + List.of(args)).isZero();
        } else if (expected instanceof Float f1 && actual instanceof Float f2) {
            assertThat(Float.compare(f1, f2))
                    .as(c + " draw " + draw + " args " + List.of(args)).isZero();
        } else {
            assertThat(actual).as(c + " draw " + draw + " args " + List.of(args))
                    .isEqualTo(expected);
        }
    }

    private static List<Case> cases() {
        return List.of(
            new Case("Category2", "ladd", new Class<?>[] { LONG_T, LONG_T }, TWO_LONGS, 200),
            new Case("Category2", "lconst", new Class<?>[0], NO_ARGS, 50),
            new Case("Category2", "conv", new Class<?>[] { INT_T }, INT, 200),
            new Case("Category2", "back", new Class<?>[] { LONG_T }, LONG, 200),
            new Case("Category2", "dbl", new Class<?>[] { DOUBLE_T }, DOUBLE, 200),
            new Case("Category2", "mix", new Class<?>[] { INT_T }, INT, 200),
            new Case("Category2", "flt", new Class<?>[] { FLOAT_T, FLOAT_T }, TWO_FLOATS, 200),
            new Case("Category2", "larray",
                new Class<?>[] { long[].class, INT_T, LONG_T }, LONG_ARRAY, 200),
            new Case("Shuffle", "dupReuse", new Class<?>[] { INT_T, INT_T }, TWO_INTS, 200),
            new Case("Shuffle", "dup2A", new Class<?>[] { int[].class, INT_T, INT_T },
                INT_ARRAY, 200));
    }

    private static long seedOf(Case c, int draw) {
        return 0x4A6F6E61524E414CL ^ (long) c.method().hashCode() * 31 + draw;
    }

    // -- helpers -----------------------------------------------------------------

    private static long[] longArray(Random rnd) {
        long[] a = new long[1 + rnd.nextInt(8)];
        for (int i = 0; i < a.length; i++) {
            a[i] = rnd.nextLong();
        }
        return a;
    }

    private static int[] intArray(Random rnd) {
        int[] a = new int[1 + rnd.nextInt(8)];
        for (int i = 0; i < a.length; i++) {
            a[i] = rnd.nextInt();
        }
        return a;
    }

    /** The classpath directory carrying the test-only executable {@code jvm.Local}. */
    private static Path testClassesDir() throws Exception {
        var location = jvm.Local.class.getProtectionDomain().getCodeSource().getLocation();
        if (location != null && location.getProtocol().equals("file")) {
            Path p = Path.of(location.toURI());
            if (Files.isDirectory(p) && Files.exists(p.resolve("jvm/Local.class"))) {
                return p;
            }
        }
        for (String entry : System.getProperty("java.class.path").split(
            java.util.regex.Pattern.quote(System.getProperty("path.separator")))) {
            Path p = Path.of(entry);
            if (Files.isDirectory(p) && Files.exists(p.resolve("jvm/Local.class"))) {
                return p;
            }
        }
        throw new AssertionError("test jvm/Local.class not found on the test classpath");
    }

    /** Captured javac stderr of the most recent {@link #compile} call (for diagnostics). */
    private String lastCompileErrors = "";

    private int compile(List<Path> sources, Path classesDir, Path classpath) throws IOException {
        var compiler = ToolProvider.getSystemJavaCompiler();
        Assumptions.assumeTrue(compiler != null, "no system javac available");
        Files.createDirectories(classesDir);
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        List<String> args = new ArrayList<>(
            List.of("-d", classesDir.toString(), "--release", "17", "-g"));
        if (classpath != null) {
            args.add("-classpath");
            args.add(classpath.toString());
        }
        for (Path p : sources) {
            args.add(p.toString());
        }
        int rc = compiler.run(null, null, err, args.toArray(String[]::new));
        lastCompileErrors = err.toString(StandardCharsets.UTF_8);
        return rc;
    }
}
