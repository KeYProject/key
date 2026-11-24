/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Stream;
import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Runs a corpus of boxing and unboxing programs through KeY and through the JDK. Each case is a
 * complete Java class with a JML contract for {@code m} and a {@code main} that prints the value
 * observed at run time. KeY must prove or split the contract as recorded, and the JDK run must
 * print the recorded output, so the transformation can be compared against Java's own semantics
 * without an external script or data file.
 */
class AutoboxingSemanticsTest {
    private static final String PROVABLE = "PROVABLE";
    private static final String SPLIT = "SPLIT";

    @BeforeAll
    static void enableJml() {
        var properties = new StrategyProperties();
        properties.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,
            StrategyProperties.LOOP_SCOPE_EXPAND);
        ProofSettings.DEFAULT_SETTINGS.getStrategySettings()
                .setActiveStrategyProperties(properties);
        ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setUseJML(true);
    }

    private record SemanticCase(String name, String className, String kind,
            String expectedOutput, String source) {
    }

    private static final List<SemanticCase> CASES = List.of(
        new SemanticCase("explicit-int", "ExplicitInt", PROVABLE, "int=42", """
                public class ExplicitInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = Integer.valueOf(42);
                        int i = a.intValue();
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("int=" + m());
                    }
                }
                """),
        new SemanticCase("explicit-long", "ExplicitLong", PROVABLE, "long=42", """
                public class ExplicitLong {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static long m() {
                        Long a = Long.valueOf(42L);
                        long i = a.longValue();
                        //@ assert i == 42L;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("long=" + m());
                    }
                }
                """),
        new SemanticCase("explicit-null", "ExplicitNull", SPLIT, "npe", """
                public class ExplicitNull {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = null;
                        int i = a.intValue();
                        return i;
                    }

                    public static void main(String[] args) {
                        try {
                            m();
                            System.out.println("no-npe");
                        } catch (NullPointerException e) {
                            System.out.println("npe");
                        }
                    }
                }
                """),
        new SemanticCase("uniform-int", "UniformInt", PROVABLE, "int=42", """
                public class UniformInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 42;
                        int i = a;
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("int=" + m());
                    }
                }
                """),
        new SemanticCase("uniform-long", "UniformLong", PROVABLE, "long=42", """
                public class UniformLong {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static long m() {
                        Long a = 42L;
                        long i = a;
                        //@ assert i == 42L;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("long=" + m());
                    }
                }
                """),
        new SemanticCase("null-int", "NullInt", SPLIT, "npe", """
                public class NullInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = null;
                        int i = a;
                        return i;
                    }

                    public static void main(String[] args) {
                        try {
                            m();
                            System.out.println("no-npe");
                        } catch (NullPointerException e) {
                            System.out.println("npe");
                        }
                    }
                }
                """),
        new SemanticCase("field-int", "FieldInt", PROVABLE, "field=42", """
                public class FieldInt {
                    Integer f;

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public int m() {
                        f = 42;
                        int i = f;
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("field=" + new FieldInt().m());
                    }
                }
                """),
        new SemanticCase("return-int", "ReturnInt", PROVABLE, "return=42", """
                public class ReturnInt {
                    static Integer box() {
                        return 42;
                    }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        int i = box();
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("return=" + m());
                    }
                }
                """),
        new SemanticCase("arg-int", "ArgInt", PROVABLE, "arg=42", """
                public class ArgInt {
                    static int id(Integer x) {
                        return x;
                    }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        int i = id(42);
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("arg=" + m());
                    }
                }
                """),
        new SemanticCase("arg-null", "ArgNull", SPLIT, "npe", """
                public class ArgNull {
                    static int id(int x) {
                        return x;
                    }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = null;
                        return id(a);
                    }

                    public static void main(String[] args) {
                        try {
                            m();
                            System.out.println("no-npe");
                        } catch (NullPointerException e) {
                            System.out.println("npe");
                        }
                    }
                }
                """),
        new SemanticCase("varargs-int", "VarargsInt", PROVABLE, "varargs=42", """
                public class VarargsInt {
                    static int first(Integer... xs) {
                        return xs[0];
                    }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        int i = first(42);
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("varargs=" + m());
                    }
                }
                """),
        new SemanticCase("promotion-int", "PromotionInt", PROVABLE, "promotion=43", """
                public class PromotionInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 42;
                        int i = a + 1;
                        //@ assert i == 43;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("promotion=" + m());
                    }
                }
                """),
        new SemanticCase("promotion-long", "PromotionLong", PROVABLE, "long=43", """
                public class PromotionLong {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static long m() {
                        Integer a = 42;
                        long v = a + 1L;
                        //@ assert v == 43L;
                        return v;
                    }

                    public static void main(String[] args) {
                        System.out.println("long=" + m());
                    }
                }
                """),
        new SemanticCase("condition-bool", "ConditionBool", PROVABLE, "condition=1", """
                public class ConditionBool {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Boolean z = true;
                        int i = 0;
                        if (z) {
                            i = 1;
                        }
                        //@ assert i == 1;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("condition=" + m());
                    }
                }
                """),
        new SemanticCase("index-int", "IndexInt", PROVABLE, "index=6", """
                public class IndexInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer idx = 1;
                        int[] values = new int[] { 5, 6, 7 };
                        int x = values[idx];
                        //@ assert x == 6;
                        return x;
                    }

                    public static void main(String[] args) {
                        System.out.println("index=" + m());
                    }
                }
                """),
        new SemanticCase("switch-int", "SwitchInt", PROVABLE, "switch=2", """
                public class SwitchInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 2;
                        int r = 0;
                        switch (a) {
                            case 1: r = 1; break;
                            case 2: r = 2; break;
                            default: r = 0; break;
                        }
                        //@ assert r == 2;
                        return r;
                    }

                    public static void main(String[] args) {
                        System.out.println("switch=" + m());
                    }
                }
                """),
        new SemanticCase("compound-int", "CompoundInt", PROVABLE, "compound=43", """
                public class CompoundInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 42;
                        a += 1;
                        int i = a;
                        //@ assert i == 43;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("compound=" + m());
                    }
                }
                """),
        new SemanticCase("postfix-int", "PostfixInt", PROVABLE, "postfix=85", """
                public class PostfixInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 42;
                        int i = a++;
                        int j = a;
                        //@ assert i == 42;
                        //@ assert j == 43;
                        return i + j;
                    }

                    public static void main(String[] args) {
                        System.out.println("postfix=" + m());
                    }
                }
                """),
        new SemanticCase("prefix-int", "PrefixInt", PROVABLE, "prefix=43", """
                public class PrefixInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 42;
                        int i = ++a;
                        //@ assert i == 43;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("prefix=" + m());
                    }
                }
                """),
        new SemanticCase("increment-sum", "IncrementSum", PROVABLE, "sum=129", """
                public class IncrementSum {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 42;
                        int i = a++ + a++;
                        int j = a;
                        //@ assert i == 85;
                        //@ assert j == 44;
                        return i + j;
                    }

                    public static void main(String[] args) {
                        System.out.println("sum=" + m());
                    }
                }
                """),
        new SemanticCase("postfix-call", "PostfixCall", PROVABLE, "call=85", """
                public class PostfixCall {
                    static int id(int x) {
                        return x;
                    }

                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 42;
                        int i = id(a++);
                        int j = a;
                        //@ assert i == 42;
                        //@ assert j == 43;
                        return i + j;
                    }

                    public static void main(String[] args) {
                        System.out.println("call=" + m());
                    }
                }
                """),
        new SemanticCase("cast-unbox", "CastUnbox", PROVABLE, "cast=42", """
                public class CastUnbox {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 42;
                        int i = (int) a;
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("cast=" + m());
                    }
                }
                """),
        new SemanticCase("cast-object", "CastObject", PROVABLE, "object=nonnull", """
                public class CastObject {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static void m() {
                        Object o = (Object) 42;
                        //@ assert o != null;
                    }

                    public static void main(String[] args) {
                        m();
                        System.out.println("object=nonnull");
                    }
                }
                """),
        new SemanticCase("number-int", "NumberInt", PROVABLE, "number=nonnull", """
                public class NumberInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static void m() {
                        Number n = 42;
                        //@ assert n != null;
                    }

                    public static void main(String[] args) {
                        m();
                        System.out.println("number=nonnull");
                    }
                }
                """),
        new SemanticCase("conditional-int", "ConditionalInt", PROVABLE, "cond=42", """
                public class ConditionalInt {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer a = 42;
                        boolean f = true;
                        int i = f ? a : 0;
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("cond=" + m());
                    }
                }
                """),
        new SemanticCase("conditional-box", "ConditionalBox", PROVABLE, "box=42", """
                public class ConditionalBox {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        boolean f = false;
                        Integer a = f ? 1 : Integer.valueOf(42);
                        int i = a;
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("box=" + m());
                    }
                }
                """),
        new SemanticCase("array-literal", "ArrayLiteral", PROVABLE, "array=2", """
                public class ArrayLiteral {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer[] xs = { 1, 2 };
                        int i = xs[1];
                        //@ assert i == 2;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("array=" + m());
                    }
                }
                """),
        new SemanticCase("array-store", "ArrayStore", PROVABLE, "store=42", """
                public class ArrayStore {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer[] xs = new Integer[2];
                        xs[0] = 42;
                        int i = xs[0];
                        //@ assert i == 42;
                        return i;
                    }

                    public static void main(String[] args) {
                        System.out.println("store=" + m());
                    }
                }
                """),
        new SemanticCase("array-unbox-store", "ArrayUnboxStore", PROVABLE, "unboxstore=42", """
                public class ArrayUnboxStore {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        int[] a = new int[1];
                        Integer x = 42;
                        a[0] = x;
                        //@ assert a[0] == 42;
                        return a[0];
                    }

                    public static void main(String[] args) {
                        System.out.println("unboxstore=" + m());
                    }
                }
                """),
        new SemanticCase("foreach-box", "ForeachBox", PROVABLE, "foreachbox=6", """
                public class ForeachBox {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        int[] a = { 1, 2, 3 };
                        int s = 0;
                        for (Integer x : a) {
                            s += x;
                        }
                        //@ assert s == 6;
                        return s;
                    }

                    public static void main(String[] args) {
                        System.out.println("foreachbox=" + m());
                    }
                }
                """),
        new SemanticCase("foreach-unbox", "ForeachUnbox", PROVABLE, "foreachunbox=6", """
                public class ForeachUnbox {
                    /*@ normal_behavior
                      @ requires true;
                      @ ensures true;
                      @*/
                    public static int m() {
                        Integer[] a = { 1, 2, 3 };
                        int s = 0;
                        for (int x : a) {
                            s += x;
                        }
                        //@ assert s == 6;
                        return s;
                    }

                    public static void main(String[] args) {
                        System.out.println("foreachunbox=" + m());
                    }
                }
                """));

    @TestFactory
    Stream<DynamicTest> corpus() {
        return CASES.stream()
                .map(c -> DynamicTest.dynamicTest(c.name(), () -> runCase(c)));
    }

    private static void runCase(SemanticCase c) throws Exception {
        Path dir = Files.createTempDirectory("autoboxing-" + c.name());
        try {
            runInKey(c, dir);
            runOnJdk(c, dir);
        } finally {
            deleteRecursively(dir);
        }
    }

    private static void runInKey(SemanticCase c, Path dir) throws Exception {
        Path file = dir.resolve(c.className() + ".java");
        Files.writeString(file, c.source());
        KeYEnvironment<?> env = KeYEnvironment.load(file);
        try {
            Contract contract = env.getProofContracts().stream()
                    .filter(candidate -> candidate.getTarget() instanceof IProgramMethod method
                            && method.getMethodDeclaration().getName().equals("m"))
                    .findFirst()
                    .orElseThrow(() -> new AssertionError(
                        "no contract for method m in " + c.name()));
            Proof proof = env.createProof(contract.createProofObl(env.getInitConfig()));
            ProofStarter starter = new ProofStarter(false);
            starter.init(proof);
            starter.start();

            switch (c.kind()) {
                case PROVABLE -> assertTrue(proof.closed(),
                    () -> c.name() + " must be provable, open goals: " + proof.openGoals());
                case SPLIT -> {
                    assertFalse(proof.closed(), () -> c.name() + " must split, but closed");
                    assertTrue(anyOpenGoalMentionsNull(proof),
                        () -> c.name() + " must leave a null obligation, open goals: "
                            + proof.openGoals());
                }
                default -> throw new AssertionError("unknown corpus kind: " + c.kind());
            }
        } finally {
            env.dispose();
        }
    }

    private static boolean anyOpenGoalMentionsNull(Proof proof) {
        for (var goal : proof.openGoals()) {
            String label = goal.node().getNodeInfo().getBranchLabel();
            if (label != null && label.contains("Null")) {
                return true;
            }
            if (goal.sequent().succedent().isEmpty()
                    || goal.sequent().toString().contains("null")) {
                return true;
            }
        }
        return false;
    }

    /**
     * Compiles and runs the case with the JDK in this process, so the expected output is checked
     * against the real Java semantics instead of being trusted as a literal.
     */
    private static void runOnJdk(SemanticCase c, Path dir) throws Exception {
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        assertNotNull(compiler, "a JDK is required to run the Java baseline");
        Path classes = Files.createDirectories(dir.resolve("classes"));
        Path file = dir.resolve(c.className() + ".java");
        Files.writeString(file, c.source());
        int status = compiler.run(null, null, null, "--release", "21", "-proc:none",
            "-d", classes.toString(), file.toString());
        assertEquals(0, status, () -> c.name() + " must compile with javac");
        assertEquals(c.expectedOutput(), runMain(c.className(), classes),
            () -> c.name() + " must print the recorded output");
    }

    private static String runMain(String className, Path classes) throws Exception {
        URL[] classPath = { classes.toUri().toURL() };
        try (URLClassLoader loader =
            new URLClassLoader(classPath, ClassLoader.getPlatformClassLoader())) {
            Class<?> mainClass = loader.loadClass(className);
            ByteArrayOutputStream captured = new ByteArrayOutputStream();
            PrintStream original = System.out;
            try (PrintStream out = new PrintStream(captured, true, StandardCharsets.UTF_8)) {
                System.setOut(out);
                try {
                    mainClass.getMethod("main", String[].class)
                            .invoke(null, (Object) new String[0]);
                } catch (InvocationTargetException e) {
                    throw new AssertionError(className + " threw " + e.getCause(), e.getCause());
                }
            } finally {
                System.setOut(original);
            }
            return captured.toString(StandardCharsets.UTF_8).strip();
        }
    }

    private static void deleteRecursively(Path dir) throws Exception {
        try (var paths = Files.walk(dir)) {
            paths.sorted(Comparator.reverseOrder()).forEach(path -> {
                try {
                    Files.deleteIfExists(path);
                } catch (Exception e) {
                    // Best effort: the temp directory is outside the repository.
                }
            });
        }
    }
}
