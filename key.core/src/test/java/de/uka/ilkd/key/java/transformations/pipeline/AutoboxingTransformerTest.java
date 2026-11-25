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
    void narrowsCharConstantBeforeBoxing() {
        String out = rewrite("void m() { Character c = 65; }");
        assertTrue(out.contains("Character.valueOf((char) 65)"), out);
    }

    @Test
    void narrowsShortConstantToByte() {
        String out = rewrite("void m() { Byte b = (short) 1; }");
        assertTrue(out.contains("Byte.valueOf((byte) (short) 1)"), out);
    }

    @Test
    void narrowsByteConstantToShort() {
        String out = rewrite("void m() { Short s = (byte) 1; }");
        assertTrue(out.contains("Short.valueOf((short) (byte) 1)"), out);
    }

    @Test
    void narrowsCharConstantToByte() {
        String out = rewrite("void m() { Byte b = (char) 65; }");
        assertTrue(out.contains("Byte.valueOf((byte) (char) 65)"), out);
    }

    @Test
    void refusesOutOfRangeConstant() {
        String out = rewrite("void m() { Byte b = 128; Character c = -1; }");
        assertFalse(out.contains("Byte.valueOf"), out);
        assertFalse(out.contains("Character.valueOf"), out);
    }

    @Test
    void refusesNarrowingFromLong() {
        String out = rewrite("void m() { Byte b = 1L; }");
        assertFalse(out.contains("Byte.valueOf"), out);
    }

    @Test
    void doesNotNarrowToInteger() {
        String out = rewrite("void m() { Integer i = (short) 1; }");
        assertFalse(out.contains("Integer.valueOf"), out);
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
    void unboxesArrayCreationDimension() {
        String out = rewrite("void m() { Integer n = 2; int[] a = new int[n]; }");
        assertTrue(out.contains("new int[n.value]"), out);
    }

    @Test
    void unboxesAssertCondition() {
        String out = rewrite("void m() { Boolean b = true; assert b; }");
        assertTrue(out.contains("assert b.value;"), out);
    }

    @Test
    void keepsAnnotatedArrayDimensions() {
        String out = rewrite("""
                @interface A { }
                void m() { Integer @A [] a = { 1 }; }
                """);
        assertTrue(out.contains("@A"), out);
        assertTrue(out.contains("new Integer @A []"), out);
        assertTrue(out.contains("Integer.valueOf(1)"), out);
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
    void parenthesisesConditionalBeforeUnboxing() {
        String out = rewrite("void m(boolean f, Boolean a, Boolean b) { if (f ? a : b) { } }");
        assertTrue(out.contains("if ((f ? a : b).value)"), out);
    }

    @Test
    void parenthesisesCastBeforeUnboxing() {
        String out = rewrite("void m(Boolean z) { boolean r = (Boolean) z; }");
        assertTrue(out.contains("boolean r = ((Boolean) z).value;"), out);
    }

    @Test
    void parenthesisesAssignmentBeforeUnboxing() {
        String out = rewrite("void m(Boolean b, Boolean c) { boolean r = (b = c); }");
        assertTrue(out.contains("boolean r = (b = c).value;"), out);
    }

    @Test
    void parenthesisesConditionalInUnboxingCast() {
        String out =
            rewrite("void m(Integer a, Integer b, boolean f) { int i = (int) (f ? a : b); }");
        assertTrue(out.contains("int i = (f ? a : b).value;"), out);
    }

    @Test
    void unboxesBooleanOperandOfAnd() {
        String out = rewrite(
            "void m() { Boolean b = true; boolean c = false; boolean r = b & c; }");
        assertTrue(out.contains("b.value & c"), out);
        assertFalse(out.contains(").value"), out);
    }

    @Test
    void unboxesBooleanOperandsOfOr() {
        String out = rewrite(
            "void m() { Boolean b = true; Boolean c = false; boolean r = b | c; }");
        assertTrue(out.contains("b.value | c.value"), out);
    }

    @Test
    void boxesBooleanResultOfAnd() {
        String out = rewrite(
            "void m() { Boolean b = true; Boolean c = false; Boolean r = b & c; }");
        assertTrue(out.contains("Boolean.valueOf(b.value & c.value)"), out);
    }

    @Test
    void unboxesBoxedEqualityWithPrimitive() {
        String out = rewrite("void m() { Boolean b = true; boolean r = b == true; }");
        assertTrue(out.contains("b.value == true"), out);
    }

    @Test
    void keepsBoxedBooleanEqualityByReference() {
        String out =
            rewrite("void m() { Boolean b = true; Boolean c = false; boolean r = b == c; }");
        assertFalse(out.contains("b.value"), out);
        assertFalse(out.contains("c.value"), out);
    }

    @Test
    void compoundBooleanAndOnBoxedTarget() {
        String out = rewrite("void m() { Boolean b = true; b &= true; }");
        assertTrue(out.contains("b = Boolean.valueOf(b.value & true)"), out);
    }

    @Test
    void compoundBooleanAndOnPrimitiveTarget() {
        String out = rewrite("void m() { boolean b = true; Boolean c = false; b &= c; }");
        assertTrue(out.contains("b = b & c.value"), out);
    }

    @Test
    void leavesPrimitiveBooleanCompoundAssignment() {
        String out = rewrite("void m() { boolean b = true; b &= false; }");
        assertTrue(out.contains("b &= false"), out);
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

    @Test
    void rewritesFloatPostfixStatement() {
        String out = rewrite("void m(Float f) { f++; }");
        assertTrue(out.contains("f = Float.valueOf(f.value + 1);"), out);
    }

    @Test
    void rewritesDoublePostfixDecrementStatement() {
        String out = rewrite("void m(Double d) { d--; }");
        assertTrue(out.contains("d = Double.valueOf(d.value - 1);"), out);
    }

    @Test
    void leavesFloatPostfixWithUsedValue() {
        String out = rewrite("void m(Float f) { float x = f++; }");
        assertFalse(out.contains("Float.valueOf"), out);
        assertTrue(out.contains("float x = f++;"), out);
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
    void boxesCast() {
        String out = rewrite("void m() { Integer a = (Integer) 42; }");
        assertTrue(out.contains("Integer.valueOf(42)"), out);
        assertFalse(out.contains("(Integer)"), out);
    }

    @Test
    void refusesIllegalBoxingCast() {
        String out = rewrite("""
                void m() {
                    Object o = (Integer) (short) 1;
                    Byte b = (Byte) 1;
                    Character c = (Character) 65;
                }
                """);
        assertFalse(out.contains("Integer.valueOf"), out);
        assertFalse(out.contains("Byte.valueOf"), out);
        assertFalse(out.contains("Character.valueOf"), out);
    }

    @Test
    void unboxesCast() {
        String out = rewrite("void m() { Integer a = 42; int i = (int) a; }");
        assertTrue(out.contains("int i = a.value;"), out);
    }

    @Test
    void unboxesAndWidensCast() {
        String out = rewrite("void m() { Integer a = 42; long v = (long) a; }");
        assertTrue(out.contains("(long) a.value"), out);
    }

    @Test
    void boxesCastToReference() {
        String out = rewrite("void m() { Object o = (Object) 42; }");
        assertTrue(out.contains("(Object) Integer.valueOf(42)"), out);
    }

    @Test
    void boxesExactPrimitiveCastToReference() {
        String out = rewrite("void m() { Object o = (Object) (short) 1; }");
        assertTrue(out.contains("(Object) Short.valueOf((short) 1)"), out);
    }

    @Test
    void parenthesisesNarrowingCastOfBinaryExpression() {
        String out = rewrite("void m() { Byte b = 1 + 2; }");
        assertTrue(out.contains("Byte.valueOf((byte) (1 + 2))"), out);
    }

    @Test
    void parenthesisesConditionalCastOperand() {
        String out = rewrite("void m() { boolean f = true; Object o = (Object) (f ? 1 : 2); }");
        assertTrue(out.contains("(Object) Integer.valueOf((f ? 1 : 2))"), out);
    }

    @Test
    void unboxesCastOperandBeforeBoxing() {
        String out = rewrite("void m() { Integer a = 1; Integer i = (Integer) (a + 1); }");
        assertTrue(out.contains("Integer.valueOf((a.value + 1))"), out);
    }

    @Test
    void rewritesIncrementInBoxingCast() {
        String out = rewrite("void m() { Integer a = 1; Integer i = (Integer) a++; }");
        assertTrue(out.contains("Integer.valueOf"), out);
        assertTrue(out.contains("a.value + 1"), out);
    }

    @Test
    void keepsIdentityCastOnWrapper() {
        String out = rewrite("void m() { Integer a = 1; Integer i = (Integer) a; }");
        assertTrue(out.contains("(Integer) a"), out);
        assertFalse(out.contains("a.value"), out);
    }

    @Test
    void unboxesOperandOfReferenceCast() {
        String out = rewrite("void m() { Integer a = 1; Object o = (Object) (a + 1); }");
        assertTrue(out.contains("(Object) Integer.valueOf((a.value + 1))"), out);
    }

    @Test
    void boxesAssignmentToNumber() {
        String out = rewrite("void m() { Number n = 42; }");
        assertTrue(out.contains("Number n = Integer.valueOf(42)"), out);
    }

    @Test
    void unboxesNumericConditional() {
        String out = rewrite("void m() { Integer a = 42; boolean f = true; int i = f ? a : 0; }");
        assertTrue(out.contains("f ? a.value : 0"), out);
    }

    @Test
    void boxesNumericConditionalResult() {
        String out = rewrite("void m() { boolean f = true; Integer a = f ? 1 : 2; }");
        assertTrue(out.contains("f ? Integer.valueOf(1) : Integer.valueOf(2)"), out);
    }

    @Test
    void boxesNumericConditionalBranch() {
        String out = rewrite(
            "void m() { Integer a = 1; boolean f = true; Integer c = f ? a : 2; }");
        assertTrue(out.contains("f ? Integer.valueOf(a.value) : Integer.valueOf(2)"), out);
    }

    @Test
    void keepsBothBoxedConditionalByReference() {
        String out = rewrite(
            "void m() { Integer a = 1; Integer b = 2; boolean f = true; Integer c = f ? a : b; }");
        assertTrue(out.contains("f ? a : b"), out);
        assertFalse(out.contains("a.value"), out);
        assertFalse(out.contains("b.value"), out);
    }

    @Test
    void keepsBothBoxedBooleanConditionalByReference() {
        String out = rewrite("""
                void m() {
                    Boolean a = true; Boolean b = false; boolean f = true; Boolean c = f ? a : b;
                }
                """);
        assertTrue(out.contains("f ? a : b"), out);
        assertFalse(out.contains("a.value"), out);
        assertFalse(out.contains("b.value"), out);
    }

    @Test
    void unboxesBothBoxedConditionalResult() {
        String out = rewrite(
            "void m() { Integer a = 1; Integer b = 2; boolean f = true; int i = f ? a : b; }");
        assertTrue(out.contains("(f ? a : b).value"), out);
        assertFalse(out.contains("a.value"), out);
        assertFalse(out.contains("b.value"), out);
    }

    @Test
    void rewritesNestedConversionsInUnboxedConditional() {
        String out = rewrite("""
                Integer id(Integer x) { return x; }
                void m() { Integer a = 1; boolean f = true; int i = f ? id(2) : a; }
                """);
        assertTrue(out.contains("(f ? id(Integer.valueOf(2)) : a).value"), out);
    }

    @Test
    void boxesNullConditionalBranch() {
        String out = rewrite("void m() { boolean f = true; Integer c = f ? null : 1; }");
        assertTrue(out.contains("f ? null : Integer.valueOf(1)"), out);
    }

    @Test
    void boxesPrimitiveBranchOfReferenceConditional() {
        String out =
            rewrite("void m() { Object x = null; boolean f = true; Object c = f ? x : 1; }");
        assertTrue(out.contains("f ? x : Integer.valueOf(1)"), out);
    }

    @Test
    void boxesBooleanConditionalBranch() {
        String out = rewrite(
            "void m() { Boolean a = true; boolean f = true; Boolean c = f ? a : false; }");
        assertTrue(out.contains("f ? Boolean.valueOf(a.value) : Boolean.valueOf(false)"), out);
    }

    @Test
    void boxesBooleanResultWithoutPrimitiveBranch() {
        String out = rewrite("""
                void m() {
                    Boolean a = true; Boolean b = false; boolean f = true; Boolean c = f ? a : b;
                }
                """);
        assertTrue(out.contains("c = f ? a : b"), out);
    }

    @Test
    void appliesConstantByteRuleToConditional() {
        String out = rewrite("void m() { Byte b = 1; boolean f = true; int i = f ? b : 0; }");
        assertTrue(out.contains("int i = f ? b.value : 0;"), out);
    }

    @Test
    void unboxesBooleanConditional() {
        String out = rewrite(
            "void m() { Boolean z = true; boolean f = true; boolean b = z ? f : false; }");
        assertTrue(out.contains("z.value ? f : false"), out);
    }

    @Test
    void boxesArrayInitializer() {
        String out = rewrite("void m() { Integer[] xs = { 1, 2 }; }");
        assertTrue(out.contains("Integer.valueOf(1)"), out);
        assertTrue(out.contains("Integer.valueOf(2)"), out);
    }

    @Test
    void boxesArrayInitializerToObject() {
        String out = rewrite("void m() { Object[] xs = { 1 }; }");
        assertTrue(out.contains("Integer.valueOf(1)"), out);
    }

    @Test
    void boxesNestedArrayInitializer() {
        String out = rewrite("void m() { Integer[][] xs = { { 1 }, { 2 } }; }");
        assertTrue(out.contains("Integer.valueOf(1)"), out);
        assertTrue(out.contains("Integer.valueOf(2)"), out);
    }

    @Test
    void boxesArrayStore() {
        String out = rewrite("void m() { Integer[] xs = new Integer[2]; xs[0] = 1; }");
        assertTrue(out.contains("xs[0] = Integer.valueOf(1)"), out);
    }

    @Test
    void unboxesArrayRead() {
        String out = rewrite("void m() { Integer[] xs = new Integer[1]; int i = xs[0]; }");
        assertTrue(out.contains("xs[0].value"), out);
    }

    @Test
    void unboxesArrayStoreFromBoxed() {
        String out = rewrite("void m() { int[] a = new int[1]; Integer x = 42; a[0] = x; }");
        assertTrue(out.contains("a[0] = x.value"), out);
    }

    @Test
    void boxesEnhancedForArrayElement() {
        String out = rewrite("void m() { int[] a = new int[1]; for (Integer x : a) { } }");
        assertTrue(out.contains("$keYIndex"), out);
        assertTrue(out.contains("Integer.valueOf"), out);
        assertTrue(out.contains(".length"), out);
    }

    @Test
    void unboxesEnhancedForArrayElement() {
        String out = rewrite("void m() { Integer[] a = new Integer[1]; for (int x : a) { } }");
        assertTrue(out.contains("$keYIndex"), out);
        assertTrue(out.contains(".value"), out);
    }

    @Test
    void evaluatesEnhancedForIterableOnce() {
        String out = rewrite("""
                void m() {
                    int[] a = new int[1];
                    for (Integer x : a) {
                        a = new int[] { 9 };
                    }
                }
                """);
        assertTrue(out.contains("var $keYArray1 = a;"), out);
        assertTrue(out.contains("$keYArray1[$keYIndex1]"), out);
        assertTrue(out.contains("$keYArray1.length"), out);
    }

    @Test
    void evaluatesParenthesisedIterableOnce() {
        String out = rewrite("""
                void m() {
                    int[] a = new int[1];
                    for (Integer x : (a)) { }
                }
                """);
        assertTrue(out.contains("$keYArray"), out);
    }

    @Test
    void evaluatesCallIterableOnce() {
        String out = rewrite("""
                int[] get() { return new int[1]; }
                void m() { for (Integer x : get()) { } }
                """);
        assertTrue(out.contains("var $keYArray1 = get();"), out);
    }

    @Test
    void keepsEnhancedForWithoutConversion() {
        String out = rewrite("void m() { int[] a = new int[1]; for (int x : a) { } }");
        assertTrue(out.contains("for (int x : a)"), out);
        assertFalse(out.contains("$keYIndex"), out);
        assertFalse(out.contains("$keYArray"), out);
    }

    @Test
    void wrapsEnhancedForWithoutSurroundingBlock() {
        String out = rewrite("""
                boolean m(boolean f, int[] a) {
                    if (f)
                        for (Integer x : a) { }
                    return f;
                }
                """);
        assertTrue(out.contains("if (f) {"), out);
        assertTrue(out.contains("var $keYArray1 = a;"), out);
        assertTrue(out.contains("$keYArray1[$keYIndex1]"), out);
        assertFalse(out.contains("for (Integer x : a)"), out);
    }

    @Test
    void wrapsEnhancedForInLabeledStatement() {
        String out = rewrite("""
                void m(int[] a) {
                    label: for (Integer x : a) {
                        break label;
                    }
                }
                """);
        assertTrue(out.contains("label: {"), out);
        assertTrue(out.contains("var $keYArray1 = a;"), out);
        assertTrue(out.contains("$keYArray1[$keYIndex1]"), out);
    }

    @Test
    void keepsUnconvertedEnhancedForWithoutSurroundingBlock() {
        String out = rewrite("""
                boolean m(boolean f, int[] a) {
                    if (f)
                        for (int x : a) { }
                    return f;
                }
                """);
        assertTrue(out.contains("for (int x : a)"), out);
        assertFalse(out.contains("$keYArray"), out);
    }

    @Test
    void rewritesArrayElementIncrement() {
        String out = rewrite("void m(Integer[] arr) { arr[0]++; }");
        assertTrue(out.contains("arr[0] = Integer.valueOf"), out);
        assertTrue(out.contains("arr[0].value + 1"), out);
    }

    @Test
    void rewritesArrayElementCompoundAssignment() {
        String out = rewrite("void m(Integer[] arr) { arr[0] += 1; }");
        assertTrue(out.contains("arr[0] = Integer.valueOf"), out);
        assertTrue(out.contains("arr[0].value + 1"), out);
    }

    @Test
    void keepsArrayElementIncrementWithSideEffectingIndex() {
        String out = rewrite("void m(Integer[] arr, int i) { arr[i++]++; }");
        assertTrue(out.contains("arr[i++]++"), out);
        assertFalse(out.contains("Integer.valueOf"), out);
    }

    @Test
    void narrowsConstantVariable() {
        String out = rewrite("Byte m() { final int K = 5; Byte r = K; return r; }");
        assertTrue(out.contains("Byte r = Byte.valueOf((byte) K);"), out);
    }

    @Test
    void doesNotNarrowNonFinalVariable() {
        String out = rewrite("Byte m() { int K = 5; Byte r = K; return r; }");
        assertFalse(out.contains("Byte.valueOf"), out);
    }

    @Test
    void doesNotNarrowOutOfRangeConstantVariable() {
        String out = rewrite("Byte m() { final int K = 200; Byte r = K; return r; }");
        assertFalse(out.contains("Byte.valueOf"), out);
    }

    @Test
    void doesNotCaptureUserIdentifiers() {
        String out = rewrite("""
                void m() {
                    int[] a = new int[1];
                    int $keYArray1 = 0;
                    int $keYIndex1 = 0;
                    for (Integer x : a) { }
                }
                """);
        assertTrue(out.contains("var $keYArray1$1 = a;"), out);
        assertTrue(out.contains("$keYArray1$1[$keYIndex1$1]"), out);
    }

    @Test
    void unboxesCompoundAssignmentRhs() {
        String out = rewrite("void m() { int s = 0; Integer x = 42; s += x; }");
        assertTrue(out.contains("x.value"), out);
    }

    @Test
    void unboxesEnhancedForBody() {
        String out = rewrite(
            "void m() { int[] a = new int[1]; for (Integer x : a) { int s = 0; s += x; } }");
        assertTrue(out.contains("x.value"), out);
    }

    @Test
    void unboxesEnhancedForBodyWithOuterLocal() {
        String out = rewrite("""
                void m() {
                    int[] a = new int[1];
                    int s = 0;
                    for (Integer x : a) {
                        s += x;
                    }
                }
                """);
        assertTrue(out.contains("x.value"), out);
    }

    @Test
    void explicitCallsAreIdempotent() {
        String out = rewrite(
            "void m() { Integer a = Integer.valueOf(42); int i = a.intValue(); }");
        assertTrue(out.contains("Integer.valueOf(42)"), out);
        assertTrue(out.contains("a.intValue()"), out);
        assertFalse(out.contains("a.value"), out);
    }

    @Test
    void keepsPrimitiveCharConditional() {
        String out = rewrite("void m(boolean f, char x, char y) { char c = f ? x : y; }");
        assertTrue(out.contains("char c = f ? x : y;"), out);
        assertFalse(out.contains("(int)"), out);
    }

    @Test
    void keepsPrimitiveByteAndShortConditionals() {
        String out = rewrite("""
                void m(boolean f, byte x, byte y, short u, short v) {
                    byte b = f ? x : y;
                    short s = f ? u : v;
                }
                """);
        assertTrue(out.contains("byte b = f ? x : y;"), out);
        assertTrue(out.contains("short s = f ? u : v;"), out);
    }

    @Test
    void widensByteBranchToShortConditional() {
        String out =
            rewrite("void m(boolean f, byte x, short y) { short s = f ? x : y; }");
        assertTrue(out.contains("short s = f ? (short) x : y;"), out);
    }

    @Test
    void boxesConstantByteConditional() {
        String out = rewrite("void m(boolean f, byte x) { Object o = f ? x : 2; }");
        assertTrue(out.contains("f ? Byte.valueOf(x) : Byte.valueOf((byte) 2)"), out);
    }

    @Test
    void refusesConstantByteConditionalAboveRange() {
        String out = rewrite("void m(boolean f, byte x) { Object o = f ? x : 200; }");
        assertTrue(out.contains("Integer.valueOf((int) x)"), out);
        assertTrue(out.contains("Integer.valueOf(200)"), out);
    }

    @Test
    void promotesBoxedByteAndShortToShort() {
        String out =
            rewrite("void m(boolean f, Byte x, Short y) { Object o = f ? x : y; }");
        assertTrue(out.contains("Short.valueOf((short) x.value)"), out);
        assertTrue(out.contains("Short.valueOf(y.value)"), out);
    }

    @Test
    void promotesByteBranchToShortConditionalForObject() {
        String out =
            rewrite("void m(boolean f, byte x) { Object o = f ? x : (short) 2; }");
        assertTrue(out.contains("Short.valueOf((short) x)"), out);
        assertTrue(out.contains("Short.valueOf((short) 2)"), out);
        assertFalse(out.contains("Byte.valueOf"), out);
    }

    @Test
    void widensBoxedIntegerAndLongConditional() {
        String out = rewrite("void m(boolean f, Integer x, Long y) { long v = f ? x : y; }");
        assertTrue(out.contains("long v = f ? (long) x.value : y.value;"), out);
    }

    @Test
    void boxesBoxedIntegerAndLongConditional() {
        String out = rewrite("void m(boolean f, Integer x, Long y) { Object o = f ? x : y; }");
        assertTrue(out.contains("Long.valueOf((long) x.value)"), out);
        assertTrue(out.contains("Long.valueOf(y.value)"), out);
    }

    @Test
    void boxesCharConditional() {
        String out = rewrite("void m(boolean f) { Object o = f ? ',' : ';'; }");
        assertTrue(out.contains("Character.valueOf(',')"), out);
        assertTrue(out.contains("Character.valueOf(';')"), out);
    }

    @Test
    void promotesBoxedIntegerAndCharacterToInt() {
        String out =
            rewrite("void m(boolean f, Integer x, Character y) { Object o = f ? x : y; }");
        assertTrue(out.contains("Integer.valueOf(x.value)"), out);
        assertTrue(out.contains("Integer.valueOf((int) y.value)"), out);
    }

    @Test
    void appliesConstantCharRule() {
        String out = rewrite("void m(boolean f, char x) { Object o = f ? x : 65; }");
        assertTrue(out.contains("Character.valueOf(x)"), out);
        assertTrue(out.contains("Character.valueOf((char) 65)"), out);
    }

    @Test
    void refusesConstantCharRuleAboveRange() {
        String out = rewrite("void m(boolean f, char x) { Object o = f ? x : 65536; }");
        assertTrue(out.contains("Integer.valueOf((int) x)"), out);
        assertTrue(out.contains("Integer.valueOf(65536)"), out);
    }

    @Test
    void constantRuleRequiresIntOperand() {
        String out =
            rewrite("void m(boolean f, char x) { Object o = f ? x : (short) 2; }");
        assertTrue(out.contains("Integer.valueOf((int) x)"), out);
        assertTrue(out.contains("Integer.valueOf((int) (short) 2)"), out);
        assertFalse(out.contains("Character.valueOf"), out);
    }

    @Test
    void keepsBothBoxedIntegerConditionalByReferenceForJlsRuleOne() {
        String out = rewrite("""
                void m(boolean f, Integer a, Integer b) {
                    Integer c = f ? a : b;
                }
                """);
        assertTrue(out.contains("Integer c = f ? a : b;"), out);
        assertFalse(out.contains("valueOf"), out);
        assertFalse(out.contains(".value"), out);
    }

    @Test
    void unboxesNullConditionalInAddition() {
        String out = rewrite("void m(boolean f) { int i = (f ? null : 1) + 1; }");
        assertTrue(out.contains("int i = (f ? null : Integer.valueOf(1)).value + 1;"), out);
    }

    @Test
    void unboxesNullConditionalInArrayIndex() {
        String out = rewrite("void m(boolean f, int[] arr) { int x = arr[f ? null : 1]; }");
        assertTrue(out.contains("arr[(f ? null : Integer.valueOf(1)).value]"), out);
    }

    @Test
    void unboxesNullBooleanConditionalInBinaryOperation() {
        String out = rewrite("void m(boolean f) { Boolean b = (f ? null : true) & false; }");
        assertTrue(out
                .contains("Boolean.valueOf((f ? null : Boolean.valueOf(true)).value & false)"),
            out);
    }

    @Test
    void unboxesNullConditionalInUnary() {
        String out = rewrite("void m(boolean f) { int i = -(f ? null : 1); }");
        assertTrue(out.contains("-(f ? null : Integer.valueOf(1)).value"), out);
    }

    @Test
    void unboxesNullConditionalInComparison() {
        String out = rewrite("void m(boolean f) { boolean r = (f ? null : 1) == 2; }");
        assertTrue(out.contains("(f ? null : Integer.valueOf(1)).value == 2"), out);
    }

    @Test
    void unboxesNullConditionalInShift() {
        String out = rewrite("void m(boolean f) { int i = (f ? null : 1) << 1; }");
        assertTrue(out.contains("(f ? null : Integer.valueOf(1)).value << 1"), out);
    }

    @Test
    void unboxesNullBooleanConditionalInIfCondition() {
        String out = rewrite("void m(boolean f) { if (f ? null : true) { } }");
        assertTrue(out.contains("if ((f ? null : Boolean.valueOf(true)).value)"), out);
    }

    @Test
    void unboxesNullConditionalInCompoundAssignment() {
        String out = rewrite("void m(boolean f) { int a = 0; a += (f ? null : 1); }");
        assertTrue(out.contains("a = (int) (a + (f ? null : Integer.valueOf(1)).value);"), out);
    }
}
