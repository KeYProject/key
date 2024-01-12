/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.util.Arrays;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.SpecMathMode;
import de.uka.ilkd.key.util.RecognitionException;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * This class provides tests for parsing int, long, and char literals.
 *
 * @author Wolfram Pfeifer
 */
public class TestIntLiteralParsing extends AbstractTestTermParser {
    // spotless:off // disable spotless to keep table like formatting of arrays
    /**
     * Some Strings representing valid int values and the expected terms created by parsing them.
     */
    static final String[] CHARSTRINGS = {
        //  input          ,       expected output
        "'a'", "C(7(9(#)))",
        "'z'", "C(2(2(1(#))))",
        "'A'", "C(5(6(#)))",
        "'Z'", "C(0(9(#)))",
        "' '", "C(2(3(#)))",
        "'\\b'", "C(8(#))",
        "'\\t'", "C(9(#))",
        "'\\n'", "C(0(1(#)))",
        "'\\f'", "C(2(1(#)))",
        "'\\r'", "C(3(1(#)))",
        "'\\\"'", "C(4(3(#)))",
        "'\\''", "C(9(3(#)))",
        "'\\\\'", "C(2(9(#)))",
        "'0'", "C(8(4(#)))",
        "'9'", "C(7(5(#)))",
        "'\\u0000'", "C(0(#))",
        "'\\uffff'", "C(5(3(5(5(6(#))))))",
        "'\u0000'", "C(0(#))",
        "'\u0394'", "C(6(1(9(#))))",        // greek uppercase delta
        "'\uffff'", "C(5(3(5(5(6(#))))))"
    };

    /**
     * Some Strings representing valid int values and the expected terms created by parsing them.
     */
    static final String[] INTSTRINGS = {
        //      input                              ,  expected output
        "0xffff_ffff", "Z(neglit(1(#)))",
        "0x000", "Z(0(#))",
        "0x8000_0000", "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "0x7fffffff", "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "2147483647", "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "-2147483648", "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "0", "Z(0(#))",
        "-0", "Z(0(#))", // minus is deleted here!
        "00", "Z(0(#))",
        "017777777777", "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "020000000000", "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "01671003245", "Z(3(3(9(4(2(8(9(4(2(#))))))))))",
        "0b0", "Z(0(#))",
        "0b01111111111111111111111111111111", "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "0b1000_0000_0000_0000_0000_0000_0000_0000", "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "0b0100100100011101", "Z(7(1(7(8(1(#))))))"
    };

    /**
     * Some Strings representing valid long values and the expected terms created by parsing them.
     */
    static final String[] LONGSTRINGS = {
        //      input                               ,       expected output
        // long versions of the Strings in INTSTRINGS should still be parseable:
        "0x000l", "Z(0(#))",
        "0x8000_0000l", "Z(8(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "0x7fffffffL", "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "2147483647L", "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "-2147483648l", "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "0l", "Z(0(#))",
        "-0L", "Z(0(#))", // minus is deleted here!
        "00L", "Z(0(#))",
        "017777777777l", "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "020000000000l", "Z(8(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "01671003245L", "Z(3(3(9(4(2(8(9(4(2(#))))))))))",
        "0b0L", "Z(0(#))",
        "0b01111111111111111111111111111111L", "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "0b1000_0000_0000_0000_0000_0000_0000_0000l", "Z(8(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "0b0100100100011101L", "Z(7(1(7(8(1(#))))))",

        // "real" longs:
        "0xffff_ffff_ffff_ffffL", "Z(neglit(1(#)))",

        "9223372036854775807L",
        "Z(7(0(8(5(7(7(4(5(8(6(3(0(2(7(3(3(2(2(9(#))))))))))))))))))))",

        "-9223372036854775808L",
        "Z(neglit(8(0(8(5(7(7(4(5(8(6(3(0(2(7(3(3(2(2(9(#)))))))))))))))))))))",

        "0b1111111111_1111111111_1111111111_1111111111_1111111111_1111111111_1111L",
        "Z(neglit(1(#)))",

        "0b1000000000_0000000000_0000000000_0000000000_0000000000_0000000000_0000L",
        "Z(neglit(8(0(8(5(7(7(4(5(8(6(3(0(2(7(3(3(2(2(9(#)))))))))))))))))))))",

        "0b0111111111_1111111111_1111111111_1111111111_1111111111_1111111111_1111L",
        "Z(7(0(8(5(7(7(4(5(8(6(3(0(2(7(3(3(2(2(9(#))))))))))))))))))))"
    };
    // spotless:on

    /**
     * These Strings represent numbers that are out of range of the int type.
     */
    private static final String[] INTRANGESTRINGS = { "-2147483649", // -2^31 - 1
        "2147483648", // 2^31
        "0x1_0000_0000", // 2^32
        "0b1_0000_0000_0000_0000_0000_0000_0000_0000", // 2^32
        "0400_0000_0000" // 2^32
    };

    /**
     * These Strings represent numbers that are out of range of the long type.
     */
    private static final String[] LONGRANGESTRINGS = { "-9_223_372_036_854_775_809L", // -2^63-1
        "9223372036854775808L", // 2^63
        "0x1_0000_0000_0000_0000L", // 2^64
        "0b10000_0000000000_0000000000_0000000000_0000000000_0000000000_0000000000L", // 2^64
        "020_0000_0000_0000_0000_0000L" // 2^64
    };

    private static final Logger LOGGER = LoggerFactory.getLogger(TestIntLiteralParsing.class);


    private final JmlIO jio;
    private static KeYJavaType containerType;
    private static ProgramVariable self;

    public TestIntLiteralParsing() {
        containerType = services.getJavaInfo().getKeYJavaType("testTermParserHeap.A");
        self = services.getJavaInfo().getCanonicalFieldProgramVariable("next", containerType);
        jio = new JmlIO().services(getServices()).classType(containerType)
                .specMathMode(SpecMathMode.BIGINT).selfVar(self);
    }


    @Override
    public Term parseTerm(String s) throws RecognitionException {
        PositionedString p = new PositionedString(s);
        /*
         * containerType and self variable are not relevant for the tests currently and can be
         * changed if needed.
         */
        return jio.parseExpression(p);
    }

    public Stream<DynamicTest> createTestCases(String[] testData) {
        return IntStream.range(0, testData.length / 2).mapToObj(i -> {
            String input = testData[i * 2];
            String expected = testData[i * 2 + 1];
            return DynamicTest.dynamicTest(input, () -> {
                String actual = parseTerm(input).toString();
                Assertions.assertEquals(expected, actual);
            });
        });
    }

    @TestFactory
    public Stream<DynamicTest> testCharLiteralParsing() {
        return createTestCases(CHARSTRINGS);
    }

    @TestFactory
    public Stream<DynamicTest> testIntLiteralParsing() throws RecognitionException {
        return createTestCases(INTSTRINGS);
    }

    @TestFactory
    public Stream<DynamicTest> testLongLiteralParsing() {
        return createTestCases(LONGSTRINGS);
    }

    /**
     * This method tests if meaningful ("out of bounds") error messages get printed for int literals
     * which are just outside the range of int.
     *
     */
    @TestFactory
    public Stream<DynamicTest> testIntRange() {
        return Arrays.stream(INTRANGESTRINGS).map(it -> DynamicTest.dynamicTest(it, () -> {
            RuntimeException ex = assertThrows(RuntimeException.class, () -> parseTerm(it));
            assertTrue(ex.getCause().getMessage().startsWith("Number constant out of bounds"));
        }));
    }

    /**
     * This method tests if meaningful ("out of bounds") error messages get printed for long
     * literals which are just outside the range of long.
     */
    @TestFactory
    public Stream<DynamicTest> testLongRange() {
        return Arrays.stream(LONGRANGESTRINGS).map(it -> DynamicTest.dynamicTest(it, () -> {
            RuntimeException ex = assertThrows(RuntimeException.class, () -> parseTerm(it));
            assertTrue(ex.getCause().getMessage().startsWith("Number constant out of bounds"));
        }));
    }
}
