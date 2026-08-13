/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.ast.JPContext;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.loader.JP2KeYConverter;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.Namespace;
import org.key_project.logic.op.sv.SchemaVariable;

import com.github.javaparser.JavaParser;
import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;
import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestInstance;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.08.26)
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class JavaMatchingTests {
    private final Services services = new Services(JavaProfile.getDefaultProfile());
    private final JPContext context;
    private final JP2KeYConverter converter;
    private final JavaParser javaParser;

    public JavaMatchingTests() {
        System.out.println("TEST INIT");
        var nss = services.getNamespaces();
        NamespaceBuilder nb = new NamespaceBuilder(nss);
        nb.addSort("boolean").addSort("int").addSort("Seq").addSort("LocSet").addSort("double")
                .addSort("float");

        @Nullable
        Namespace<SchemaVariable> nsSchema = new Namespace<>();
        nsSchema.add(SchemaVariableFactory.createProgramSV(
            new ProgramElementName("#a"), ProgramSVSort.EXPRESSION, false));
        nsSchema.add(SchemaVariableFactory.createProgramSV(
            new ProgramElementName("#b"), ProgramSVSort.EXPRESSION, false));
        nsSchema.add(SchemaVariableFactory.createProgramSV(
            new ProgramElementName("#c"), ProgramSVSort.EXPRESSION, false));

        services.activateJava(null);


        var cu = StaticJavaParser.parse("""
                public class Context {
                    int x, y, z;
                }
                """);
        services.getJavaService().getSymbolResolver().inject(cu);
        context = new JPContext((ClassOrInterfaceDeclaration) cu.types().getFirst(), cu);

        services.getJavaService().parseSpecialClasses();

        converter = services.getJavaService().getConverter(nsSchema);
        javaParser = services.getJavaService().getProgramFactory().createJavaParser();
    }

    private ProgramElement parse(String s) {
        var expression = javaParser.parseExpression(s);
        final var block = expression.getResult().get();
        block.setParentNode(context.classContext());
        var convert = (Expression) converter.process(block);
        return convert;
    }


    private @Nullable MatchConditions match(ProgramElement scheme, ProgramElement concrete) {
        final MatchConditions result = scheme.match(
            new SourceData(concrete, -1, services),
            MatchConditions.EMPTY_MATCHCONDITIONS);
        return result;
    }

    // ==================== BINARY OPERATORS: ARITHMETIC ====================

    @Test
    void testAddition() {
        var scheme = parse("#a + #b");
        var concrete = parse("x + y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testSubtraction() {
        var scheme = parse("#a - #b");
        var concrete = parse("x - y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testMultiplication() {
        var scheme = parse("#a * #b");
        var concrete = parse("x * y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testDivision() {
        var scheme = parse("#a / #b");
        var concrete = parse("x / y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testModulo() {
        var scheme = parse("#a % #b");
        var concrete = parse("x % y");
        assertNotNull(match(scheme, concrete));
    }

    // ==================== BINARY OPERATORS: LOGICAL ====================

    @Test
    void testLogicalAnd() {
        var scheme = parse("#a && #b");
        var concrete = parse("x > 0 && y < 10");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testLogicalOr() {
        var scheme = parse("#a || #b");
        var concrete = parse("x == 0 || y == 0");
        assertNotNull(match(scheme, concrete));
    }

    // ==================== BINARY OPERATORS: BITWISE ====================

    @Test
    void testBitwiseAnd() {
        var scheme = parse("#a & #b");
        var concrete = parse("x & y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testBitwiseOr() {
        var scheme = parse("#a | #b");
        var concrete = parse("x | y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testBitwiseXor() {
        var scheme = parse("#a ^ #b");
        var concrete = parse("x ^ y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testLeftShift() {
        var scheme = parse("#a << #b");
        var concrete = parse("x << 2");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testRightShift() {
        var scheme = parse("#a >> #b");
        var concrete = parse("x >> 1");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testUnsignedRightShift() {
        var scheme = parse("#a >>> #b");
        var concrete = parse("x >>> 2");
        assertNotNull(match(scheme, concrete));
    }

    // ==================== BINARY OPERATORS: COMPARISON ====================

    @Test
    void testLessThan() {
        var scheme = parse("#a < #b");
        var concrete = parse("x < y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testGreaterThan() {
        var scheme = parse("#a > #b");
        var concrete = parse("x > y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testLessThanOrEqual() {
        var scheme = parse("#a <= #b");
        var concrete = parse("x <= 10");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testGreaterThanOrEqual() {
        var scheme = parse("#a >= #b");
        var concrete = parse("y >= 5");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testEquality() {
        var scheme = parse("#a == #b");
        var concrete = parse("x == y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testInequality() {
        var scheme = parse("#a != #b");
        var concrete = parse("x != 0");
        assertNotNull(match(scheme, concrete));
    }

    // ==================== ASSIGNMENTS ====================

    @Test
    void testSimpleAssignment() {
        var scheme = parse("#a = #b");
        var concrete = parse("x = y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testAddAssignment() {
        var scheme = parse("#a += #b");
        var concrete = parse("x += y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testSubtractAssignment() {
        var scheme = parse("#a -= #b");
        var concrete = parse("x -= 5");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testMultiplyAssignment() {
        var scheme = parse("#a *= #b");
        var concrete = parse("z *= x");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testDivideAssignment() {
        var scheme = parse("#a /= #b");
        var concrete = parse("x /= 2");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testModuloAssignment() {
        var scheme = parse("#a %= #b");
        var concrete = parse("x %= 3");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testBitwiseAndAssignment() {
        var scheme = parse("#a &= #b");
        var concrete = parse("x &= y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testBitwiseOrAssignment() {
        var scheme = parse("#a |= #b");
        var concrete = parse("x |= 0xFF");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testBitwiseXorAssignment() {
        var scheme = parse("#a ^= #b");
        var concrete = parse("x ^= y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testLeftShiftAssignment() {
        var scheme = parse("#a <<= #b");
        var concrete = parse("x <<= 2");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testRightShiftAssignment() {
        var scheme = parse("#a >>= #b");
        var concrete = parse("x >>= 1");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testUnsignedRightShiftAssignment() {
        var scheme = parse("#a >>>= #b");
        var concrete = parse("x >>>= 2");
        assertNotNull(match(scheme, concrete));
    }

    // ==================== INCREMENT AND DECREMENT ====================

    @Test
    void testPrefixIncrement() {
        var scheme = parse("++#a");
        var concrete = parse("++x");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testPostfixIncrement() {
        var scheme = parse("#a++");
        var concrete = parse("x++");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testPrefixDecrement() {
        var scheme = parse("--#a");
        var concrete = parse("--x");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testPostfixDecrement() {
        var scheme = parse("#a--");
        var concrete = parse("x--");
        assertNotNull(match(scheme, concrete));
    }

    // ==================== COMBINATIONS ====================

    @Test
    void testChainedAddition() {
        var scheme = parse("#a + #b + #c");
        var concrete = parse("x + y + z");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testMixedArithmetic() {
        var scheme = parse("#a * #b + #c");
        var concrete = parse("x * y + z");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testParenthesizedExpression() {
        var scheme = parse("(#a + #b) * #c");
        var concrete = parse("(x + y) * z");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testAssignmentWithBinaryOp() {
        var scheme = parse("#a = #b + #c");
        var concrete = parse("x = y + z");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testComplexAssignment() {
        var scheme = parse("#a = #b * #c + #a");
        var concrete = parse("x = y * z + x");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testIncrementInExpression() {
        var scheme = parse("#a = #b++ + ++#c");
        var concrete = parse("x = y++ + ++z");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testCompoundAssignmentWithIncrement() {
        var scheme = parse("#a += ++#b");
        var concrete = parse("x += ++y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testComplexMixedExpression() {
        var scheme = parse("#a = (#b++ + --#c) * #a");
        var concrete = parse("x = (y++ + --z) * x");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testMultipleComparisons() {
        var scheme = parse("#a < #b && #b < #c");
        var concrete = parse("x < y && y < z");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testBitwiseCombination() {
        var scheme = parse("(#a & #b) | #c");
        var concrete = parse("(x & y) | z");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testShiftAndAdd() {
        var scheme = parse("(#a << #b) + #c");
        var concrete = parse("(x << 2) + y");
        assertNotNull(match(scheme, concrete));
    }

    @Test
    void testNoMatchDifferentOperator() {
        var scheme = parse("#a + #b");
        var concrete = parse("x * y");
        assertNull(match(scheme, concrete));
    }

    @Test
    void testOriginalExample() {
        var scheme = parse("x = #a + #b");
        var concrete = parse("x = x+y");
        final var result = match(scheme, concrete);
        assertNotNull(result);
    }
}
