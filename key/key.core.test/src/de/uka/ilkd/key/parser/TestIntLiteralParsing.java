package de.uka.ilkd.key.parser;

import org.antlr.runtime.RecognitionException;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.translation.KeYJMLParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * This class provides tests for parsing int, long, and char literals.
 * @author Wolfram Pfeifer
 */
public class TestIntLiteralParsing extends AbstractTestTermParser {
    /**
     * Some Strings representing valid int values and the expected terms created by parsing them.
     */
    static final String[] CHARSTRINGS = {
        //  input          ,       expected output
        "'a'"              ,       "C(7(9(#)))",
        "'z'"              ,       "C(2(2(1(#))))",
        "'A'"              ,       "C(5(6(#)))",
        "'Z'"              ,       "C(0(9(#)))",
        "' '"              ,       "C(2(3(#)))",
        "'\\b'"            ,       "C(8(#))",
        "'\\t'"            ,       "C(9(#))",
        "'\\n'"            ,       "C(0(1(#)))",
        "'\\f'"            ,       "C(2(1(#)))",
        "'\\r'"            ,       "C(3(1(#)))",
        "'\\\"'"           ,       "C(4(3(#)))",
        "'\\\''"           ,       "C(9(3(#)))",
        "'\\\\'"           ,       "C(2(9(#)))",
        "'0'"              ,       "C(8(4(#)))",
        "'9'"              ,       "C(7(5(#)))",
        "'\\u0000'"        ,       "C(0(#))",
        "'\\uffff'"        ,       "C(5(3(5(5(6(#))))))"
    };

    /**
     * Some Strings representing valid int values and the expected terms created by parsing them.
     */
    static final String[] INTSTRINGS = {
        //      input                              ,  expected output
        "0xffff_ffff"                              , "Z(neglit(1(#)))",
        "0x000"                                    , "Z(0(#))",
        "0x8000_0000"                              , "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "0x7fffffff"                               , "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "2147483647"                               , "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "-2147483648"                              , "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "0"                                        , "Z(0(#))",
        "-0"                                       , "Z(0(#))", // minus is deleted here!
        "00"                                       , "Z(0(#))",
        "017777777777"                             , "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "020000000000"                             , "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "01671003245"                              , "Z(3(3(9(4(2(8(9(4(2(#))))))))))",
        "0b0"                                      , "Z(0(#))",
        "0b01111111111111111111111111111111"       , "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "0b1000_0000_0000_0000_0000_0000_0000_0000", "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "0b0100100100011101"                       , "Z(7(1(7(8(1(#))))))"
    };

    /**
     * Some Strings representing valid long values and the expected terms created by parsing them.
     */
    static final String[] LONGSTRINGS = {
        //      input                               ,       expected output
        // long versions of the Strings in INTSTRINGS should still be parseable:
        "0x000l"                                    , "Z(0(#))",
        "0x8000_0000l"                              , "Z(8(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "0x7fffffffL"                               , "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "2147483647L"                               , "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "-2147483648l"                              , "Z(neglit(8(4(6(3(8(4(7(4(1(2(#))))))))))))",
        "0l"                                        , "Z(0(#))",
        "-0L"                                       , "Z(0(#))", // minus is deleted here!
        "00L"                                       , "Z(0(#))",
        "017777777777l"                             , "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "020000000000l"                             , "Z(8(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "01671003245L"                              , "Z(3(3(9(4(2(8(9(4(2(#))))))))))",
        "0b0L"                                      , "Z(0(#))",
        "0b01111111111111111111111111111111L"       , "Z(7(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "0b1000_0000_0000_0000_0000_0000_0000_0000l", "Z(8(4(6(3(8(4(7(4(1(2(#)))))))))))",
        "0b0100100100011101L"                       , "Z(7(1(7(8(1(#))))))",

        // "real" longs:
        "0xffff_ffff_ffff_ffffL"                    , "Z(neglit(1(#)))",

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

    /**
     * These Strings represent numbers that are out of range of the int type.
     */
    private static final String[] INTRANGESTRINGS = {
        "-2147483649",                                      // -2^31 - 1
        "2147483648",                                       // 2^31
        "0x1_0000_0000",                                    // 2^32
        "0b1_0000_0000_0000_0000_0000_0000_0000_0000",      // 2^32
        "0400_0000_0000"                                    // 2^32
    };

    /**
     * These Strings represent numbers that are out of range of the long type.
     */
    private static final String[] LONGRANGESTRINGS = {
        "-9_223_372_036_854_775_809L",                                                // -2^63-1
        "9223372036854775808L",                                                       // 2^63
        "0x1_0000_0000_0000_0000L",                                                   // 2^64
        "0b10000_0000000000_0000000000_0000000000_0000000000_0000000000_0000000000L", // 2^64
        "020_0000_0000_0000_0000_0000L"                                               // 2^64
    };

    /**
     * Creates a new test object for literal parsing tests.
     */
    public TestIntLiteralParsing() {
        super(TestIntLiteralParsing.class.getSimpleName());
    }

    @Override
    public Term parseTerm(String s) throws RecognitionException {
        PositionedString p = new PositionedString(s);
        /* containerType and self variable are not relevant for the tests
         * currently and can be changed if needed.
         */
        KeYJavaType containerType = services.getJavaInfo().getKeYJavaType("testTermParserHeap.A");
        ProgramVariable self =
                services.getJavaInfo().getCanonicalFieldProgramVariable("next", containerType);
        KeYJMLParser parser = new KeYJMLParser(p, getServices(), containerType, self,
                null, null, null, null);
        return parser.termexpression();
    }

    /**
     * Tests if the Strings in INTSTRINGS are parsed and converted correctly.
     * @throws RecognitionException if a parsing error occurs
     */
    public void testCharLiteralParsing() throws RecognitionException {
        Term t;
        String input;
        String actual;
        String expected;

        for (int i = 0; i < CHARSTRINGS.length / 2; i++) {
            input = CHARSTRINGS[i * 2];
            expected = CHARSTRINGS[i * 2 + 1];

            t = parseTerm(input);
            actual = t.toString();

            assertEquals(expected, actual);
        }
    }



    /**
     * Tests if the Strings in INTSTRINGS are parsed and converted correctly.
     * @throws RecognitionException if a parsing error occurs
     */
    public void testIntLiteralParsing() throws RecognitionException {
        Term t;
        String input;
        String actual;
        String expected;

        for (int i = 0; i < INTSTRINGS.length / 2; i++) {
            input = INTSTRINGS[i * 2];
            expected = INTSTRINGS[i * 2 + 1];

            t = parseTerm(input);
            actual = t.toString();

            assertEquals(expected, actual);
        }
    }


    /**
     * Tests if the Strings in LONGSTRINGS are parsed and converted correctly.
     * @throws RecognitionException if a parsing error occurs
     */
    public void testLongLiteralParsing() throws RecognitionException {
        Term t;
        String input;
        String actual;
        String expected;

        for (int i = 0; i < LONGSTRINGS.length / 2; i++) {
            input = LONGSTRINGS[i * 2];
            expected = LONGSTRINGS[i * 2 + 1];

            t = parseTerm(input);
            actual = t.toString();

            assertEquals(expected, actual);
        }
    }

    /**
     * This method tests if meaningful ("out of bounds") error messages get printed for int literals
     * which are just outside the range of int.
     * @throws RecognitionException if a parsing error occurs
     */
    public void testIntRange() throws RecognitionException {
        for (String s : INTRANGESTRINGS) {
            try {
                parseTerm(s);
                fail();
            } catch (SLTranslationException e) {
                assertTrue(e.getMessage().startsWith("Number constant out of bounds"));
            }
        }
    }

    /**
     * This method tests if meaningful ("out of bounds") error messages get printed for long
     * literals which are just outside the range of long.
     * @throws RecognitionException if a parsing error occurs
     */
    public void testLongRange() throws RecognitionException {
        for (String s : LONGRANGESTRINGS) {
            try {
                parseTerm(s);
                fail();
            } catch (SLTranslationException e) {
                assertTrue(e.getMessage().startsWith("Number constant out of bounds"));
            }
        }
    }
}
