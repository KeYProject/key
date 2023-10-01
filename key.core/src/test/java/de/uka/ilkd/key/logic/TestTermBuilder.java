/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.io.File;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TestJavaInfo;
import de.uka.ilkd.key.java.expression.literal.DoubleLiteral;
import de.uka.ilkd.key.java.expression.literal.FloatLiteral;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

public class TestTermBuilder {

    private Services services;
    private TermBuilder tb;

    @BeforeEach
    public void setUp() {
        HelperClassForTests helper = new HelperClassForTests();
        final ProofAggregate agg = helper.parse(new File(TestJavaInfo.testfile));
        services = agg.getFirstProof().getServices();
        tb = services.getTermBuilder();
    }


    /**
     * Test number conversion
     */
    private void checkDigits(Term number, int[] expected, IntegerLDT intLDT,
            boolean isNonNegative) {
        assertSame(intLDT.getNumberSymbol(), number.op());
        number = number.sub(0);

        if (!isNonNegative) {
            assertSame(intLDT.getNegativeNumberSign(), number.op());
            number = number.sub(0);
        }

        int count = expected.length;
        for (; number.arity() == 1; number = number.sub(0)) {
            assertSame(intLDT.getNumberLiteralFor(expected[--count]), number.op());
        }

        assertSame(intLDT.getNumberTerminator(), number.op());
    }

    @Test
    public void testNumberIsNegativeInt() {
        String[] numbers =
            new String[] { "-4096", "-1", "" + Integer.MIN_VALUE, "" + Long.MIN_VALUE };
        int[][] expected = new int[][] { { 4, 0, 9, 6 }, { 1 }, { 2, 1, 4, 7, 4, 8, 3, 6, 4, 8 },
            { 9, 2, 2, 3, 3, 7, 2, 0, 3, 6, 8, 5, 4, 7, 7, 5, 8, 0, 8 } };
        for (int i = 0; i < numbers.length; i++) {
            checkDigits(tb.zTerm(numbers[i]), expected[i],
                services.getTypeConverter().getIntegerLDT(), false);
        }
    }

    @Test
    public void testNumberIsPositiveInt() {
        String[] numbers =
            new String[] { "4096", "1", "0", "" + Integer.MAX_VALUE, "" + Long.MAX_VALUE };
        int[][] expected =
            new int[][] { { 4, 0, 9, 6 }, { 1 }, { 0 }, { 2, 1, 4, 7, 4, 8, 3, 6, 4, 7 },
                { 9, 2, 2, 3, 3, 7, 2, 0, 3, 6, 8, 5, 4, 7, 7, 5, 8, 0, 7 } };
        for (int i = 0; i < numbers.length; i++) {
            checkDigits(tb.zTerm(numbers[i]), expected[i],
                services.getTypeConverter().getIntegerLDT(), true);
        }
    }

    @Test
    public void testNumberIsVeryBigPositiveInteger() {
        String number = "16576152376524231864936749621436926134961274698712643261489762897364";
        int[] expected = new int[] { 1, 6, 5, 7, 6, 1, 5, 2, 3, 7, 6, 5, 2, 4, 2, 3, 1, 8, 6, 4, 9,
            3, 6, 7, 4, 9, 6, 2, 1, 4, 3, 6, 9, 2, 6, 1, 3, 4, 9, 6, 1, 2, 7, 4, 6, 9, 8, 7, 1, 2,
            6, 4, 3, 2, 6, 1, 4, 8, 9, 7, 6, 2, 8, 9, 7, 3, 6, 4 };

        checkDigits(tb.zTerm(number), expected, services.getTypeConverter().getIntegerLDT(), true);
    }


    @Test
    public void testNumberIsVerySmallNegativeInteger() {
        String number = "-16576152376524231864936749621436926134961274698712643261489762897364";
        int[] expected = new int[] { 1, 6, 5, 7, 6, 1, 5, 2, 3, 7, 6, 5, 2, 4, 2, 3, 1, 8, 6, 4, 9,
            3, 6, 7, 4, 9, 6, 2, 1, 4, 3, 6, 9, 2, 6, 1, 3, 4, 9, 6, 1, 2, 7, 4, 6, 9, 8, 7, 1, 2,
            6, 4, 3, 2, 6, 1, 4, 8, 9, 7, 6, 2, 8, 9, 7, 3, 6, 4 };
        checkDigits(tb.zTerm(number), expected, services.getTypeConverter().getIntegerLDT(), false);
    }

    private void testDoubleLongPatterns(String number) {
        double doubleVal = Double.parseDouble(number);
        Term doubleTerm = tb.dfpTerm(doubleVal);
        DoubleLiteral literal =
            services.getTypeConverter().getDoubleLDT().translateTerm(doubleTerm, null, services);
        assertEquals(doubleVal, Double.parseDouble(literal.getValue()),
            "for double value " + number);
    }

    @Test
    public void testDoubleLongPatterns() {
        testDoubleLongPatterns("1");
        testDoubleLongPatterns("0.");
        testDoubleLongPatterns("-1");
        testDoubleLongPatterns("-0.");
        testDoubleLongPatterns("123.33");
        testDoubleLongPatterns("123e-2");
        testDoubleLongPatterns("22e307");
        testDoubleLongPatterns("-22e307");
    }

    private void testFloatPatterns(String number) {
        float floatval = Float.parseFloat(number);
        Term floatTerm = tb.fpTerm(floatval);
        FloatLiteral literal =
            services.getTypeConverter().getFloatLDT().translateTerm(floatTerm, null, services);
        assertEquals(floatval, Float.parseFloat(literal.getValue()), "for double value " + number);
    }

    @Test
    public void testFloatPatterns() {
        testFloatPatterns("1");
        testFloatPatterns("0.");
        testFloatPatterns("-1");
        testFloatPatterns("-0.");
        testFloatPatterns("123.33");
        testFloatPatterns("123e-2");
        testFloatPatterns("22e37");
        testFloatPatterns("-22e37");
    }

}
