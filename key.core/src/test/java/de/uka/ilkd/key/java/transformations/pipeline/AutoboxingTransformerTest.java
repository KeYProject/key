/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.JavaParser;
import com.github.javaparser.ParseResult;
import com.github.javaparser.ParserConfiguration;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.symbolsolver.JavaSymbolSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.CombinedTypeSolver;
import com.github.javaparser.symbolsolver.resolution.typesolvers.ReflectionTypeSolver;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * AST-level tests for the boxing/unboxing rewrite.
 */
class AutoboxingTransformerTest {

    private static final JavaParser PARSER = new JavaParser(new ParserConfiguration()
            .setLanguageLevel(ParserConfiguration.LanguageLevel.RAW)
            .setSymbolResolver(new JavaSymbolSolver(
                new CombinedTypeSolver(new ReflectionTypeSolver()))));

    private static String rewrite(String members) {
        String source = "public class T { " + members + " }";
        ParseResult<CompilationUnit> result = PARSER.parse(source);
        if (!result.isSuccessful()) {
            throw new AssertionError("Parsing failed: " + result.getProblems() + "\n" + source);
        }
        CompilationUnit cu = result.getResult().orElseThrow();
        new AutoboxingTransformer().apply(cu);
        return cu.toString();
    }

    @Test
    void boxesPrimitiveInitializer() {
        String out = rewrite("void m() { Integer a = 42; }");
        assertTrue(out.contains("Integer.valueOf(42)"), out);
    }

    @Test
    void unboxesInitializer() {
        String out = rewrite("void m() { Integer a = 42; int i = a; }");
        assertTrue(out.contains("Integer.valueOf(42)"), out);
        assertTrue(out.contains("int i = a.value;"), out);
    }

    @Test
    void widensAfterUnboxing() {
        String out = rewrite("void m() { Integer a = 42; long v = a; }");
        assertTrue(out.contains("long v = (long) a.value;"), out);
    }

    @Test
    void doesNotWidenBeforeBoxing() {
        String out = rewrite("void m() { Long l = 1; }");
        assertFalse(out.contains("Long.valueOf"), out);
        assertTrue(out.contains("Long l = 1;"), out);
    }

    @Test
    void narrowsConstantBeforeBoxing() {
        String out = rewrite("void m() { Byte b = 1; Short s = 2; }");
        assertTrue(out.contains("Byte.valueOf((byte) 1)"), out);
        assertTrue(out.contains("Short.valueOf((short) 2)"), out);
    }

    @Test
    void fieldAssignmentBoxes() {
        String out = rewrite("Integer f; void m() { f = 7; }");
        assertTrue(out.contains("f = Integer.valueOf(7);"), out);
    }

    @Test
    void fieldInitializerBoxes() {
        String out = rewrite("static final Integer X = 42;");
        assertTrue(out.contains("Integer.valueOf(42)"), out);
    }

    @Test
    void returnBoxes() {
        String out = rewrite("Integer m() { return 42; }");
        assertTrue(out.contains("return Integer.valueOf(42);"), out);
    }

    @Test
    void varIsNotTouched() {
        String out = rewrite("void m() { var a = 42; var b = a; }");
        assertFalse(out.contains("valueOf"), out);
        assertFalse(out.contains(".value"), out);
    }

    @Test
    void convertedNodesKeepAParentChain() {
        String source = "public class T { void m() { Integer a = 42; int i = a; } }";
        ParseResult<CompilationUnit> result = PARSER.parse(source);
        assertTrue(result.isSuccessful(), result.getProblems().toString());
        CompilationUnit cu = result.getResult().orElseThrow();
        new AutoboxingTransformer().apply(cu);
        for (var name : cu.findAll(com.github.javaparser.ast.expr.NameExpr.class)) {
            assertTrue(name.findCompilationUnit().isPresent(),
                () -> "detached name " + name + " (parent " + name.getParentNode() + ")");
        }
        for (var field : cu.findAll(com.github.javaparser.ast.expr.FieldAccessExpr.class)) {
            assertTrue(field.findCompilationUnit().isPresent(),
                () -> "detached field access " + field);
        }
        assertTrue(cu.toString().contains("a.value"), cu.toString());
    }

    @Test
    void unboxesMethodArgument() {
        String out = rewrite("""
                static int f(int x) { return x; }
                void m() { Integer a = 42; int i = f(a); }
                """);
        assertTrue(out.contains("f(a.value)"), out);
    }

    @Test
    void boxesMethodArgument() {
        String out = rewrite("""
                static void g(Integer x) { }
                void m() { g(42); }
                """);
        assertTrue(out.contains("g(Integer.valueOf(42))"), out);
    }

    @Test
    void boxesVarargsElements() {
        String out = rewrite("""
                static void h(Integer... xs) { }
                void m() { h(1, 2); }
                """);
        assertTrue(out.contains("h(Integer.valueOf(1), Integer.valueOf(2))"), out);
    }

    @Test
    void unboxesVarargsElements() {
        String out = rewrite("""
                static void k(int... xs) { }
                void m() { Integer a = 42; k(a, 2); }
                """);
        assertTrue(out.contains("k(a.value, 2)"), out);
    }

    @Test
    void boxesConstructorArgument() {
        String out = rewrite("""
                static class C { C(Integer x) { } }
                void m() { C c = new C(42); }
                """);
        assertTrue(out.contains("new C(Integer.valueOf(42))"), out);
    }

    @Test
    void boxesExplicitConstructorArguments() {
        String out = rewrite("""
                static class A { A(Integer x) { } }
                static class B extends A { B() { super(42); } }
                """);
        assertTrue(out.contains("super(Integer.valueOf(42))"), out);
    }

    @Test
    void unboxesArithmeticOperand() {
        String out = rewrite("void m() { Integer a = 42; int i = a + 1; }");
        assertTrue(out.contains("a.value + 1"), out);
    }

    @Test
    void promotesMixedArithmetic() {
        String out = rewrite("void m() { Integer a = 42; long v = a + 1L; }");
        assertTrue(out.contains("(long) a.value + 1L"), out);
    }

    @Test
    void keepsBoxedEqualityByReference() {
        String out = rewrite(
            "void m() { Integer a = 42; Integer b = 42; boolean r = a == b; }");
        assertFalse(out.contains("a.value"), out);
        assertFalse(out.contains("b.value"), out);
    }

    @Test
    void unboxesPrimitiveEquality() {
        String out = rewrite("void m() { Integer a = 42; boolean r = a == 42; }");
        assertTrue(out.contains("a.value == 42"), out);
    }

    @Test
    void promotesShift() {
        String out = rewrite("void m() { Integer a = 42; long v = a << 2; }");
        assertTrue(out.contains("a.value << 2"), out);
    }

    @Test
    void unboxesArrayIndex() {
        String out = rewrite("void m() { int[] arr = new int[3]; Integer a = 1; int x = arr[a]; }");
        assertTrue(out.contains("arr[a.value]"), out);
    }

    @Test
    void unboxesSwitchSelector() {
        String out = rewrite(
            "void m() { Integer a = 1; switch (a) { case 1: break; default: break; } }");
        assertTrue(out.contains("switch(a.value)"), out);
    }

    @Test
    void unboxesUnaryOperand() {
        String out = rewrite("void m() { Integer a = 42; int i = -a; }");
        assertTrue(out.contains("-a.value"), out);
    }

    @Test
    void unboxesBooleanCondition() {
        String out = rewrite("void m() { Boolean z = true; if (z) { } }");
        assertTrue(out.contains("if (z.value)"), out);
    }

    @Test
    void unboxesBooleanNot() {
        String out = rewrite("void m() { Boolean z = true; boolean b = !z; }");
        assertTrue(out.contains("!z.value"), out);
    }

    @Test
    void compoundAssignment() {
        String out = rewrite("void m() { Integer a = 42; a += 1; }");
        assertTrue(out.contains("Integer.valueOf"), out);
        assertTrue(out.contains("a.value + 1"), out);
    }

    @Test
    void postfixIncrementUsedAsValue() {
        String out = rewrite("void m() { Integer a = 42; int i = a++; }");
        assertTrue(out.contains("a.value + 1"), out);
        assertTrue(out.contains("- 1"), out);
    }

    @Test
    void prefixIncrementUsedAsValue() {
        String out = rewrite("void m() { Integer a = 42; int i = ++a; }");
        assertTrue(out.contains("Integer.valueOf"), out);
        assertTrue(out.contains(").value"), out);
    }

    @Test
    void incrementInsideCall() {
        String out = rewrite("""
                static int id(int x) { return x; }
                void m() { Integer a = 42; int i = id(a++); }
                """);
        assertTrue(out.contains("id("), out);
        assertTrue(out.contains("a.value + 1"), out);
        assertTrue(out.contains("- 1"), out);
    }

    @Test
    void incrementInBinaryExpression() {
        String out = rewrite("void m() { Integer a = 42; int i = a++ + a++; }");
        assertEquals(2, count(out, "a.value + 1"), out);
    }

    private static int count(String text, String needle) {
        int result = 0;
        int index = 0;
        while ((index = text.indexOf(needle, index)) >= 0) {
            result++;
            index += needle.length();
        }
        return result;
    }

    @Test
    void explicitCallsAreIdempotent() {
        String out = rewrite(
            "void m() { Integer a = Integer.valueOf(42); int i = a.intValue(); }");
        assertTrue(out.contains("Integer.valueOf(42)"), out);
        assertTrue(out.contains("a.intValue()"), out);
        assertFalse(out.contains("a.value"), out);
    }
}
