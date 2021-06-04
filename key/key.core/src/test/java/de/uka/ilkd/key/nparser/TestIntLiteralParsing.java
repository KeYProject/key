package de.uka.ilkd.key.nparser;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nparser.builder.ExpressionBuilder;
import de.uka.ilkd.key.parser.AbstractTestTermParser;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import static org.junit.Assert.*;

/**
 * This class provides tests for parsing int, long, and char literals.
 *
 * @author Wolfram Pfeifer
 * @author weigl
 */
@RunWith(Parameterized.class)
@Ignore
public class TestIntLiteralParsing extends AbstractTestTermParser {
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
    /**
     * Some Strings representing valid int values and the expected terms created by parsing them.
     */
    private static final String[] CHARSTRINGS = {
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
            "'\\\''", "C(9(3(#)))",
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

    public static int PARSEABLE = 1, ERROR = -1;
    @Parameterized.Parameter(0)
    public int type;
    @Parameterized.Parameter(2)
    public String expected;
    @Parameterized.Parameter(1)
    public String input;

    @Parameterized.Parameters(name = "{1}")
    public static Collection<Object[]> data() {
        List<Object[]> seq = new LinkedList<>();
        add(seq, PARSEABLE, INTSTRINGS);
        add(seq, PARSEABLE, LONGSTRINGS);
        add(seq, PARSEABLE, CHARSTRINGS);
        add(seq, ERROR, INTRANGESTRINGS);
        add(seq, ERROR, LONGRANGESTRINGS);
        return seq;
    }

    private static void add(List<Object[]> seq, int type, String[] cases) {
        if (type == ERROR) {
            for (String aCase : cases) seq.add(new Object[]{type, aCase, ""});
        } else {
            for (int i = 0; i < cases.length; i += 2)
                seq.add(new Object[]{type, cases[i], cases[i + 1]});
        }
    }

    private Services services = getServices();

    @Test
    public void testLex() {
        KeYLexer lexer = ParsingFacade.createLexer(CharStreams.fromString(input));
        List<? extends Token> toks = lexer.getAllTokens();
        System.out.println(toks);
        assertEquals(1, toks.size());
        int t = toks.get(0).getType();
        assertTrue("Wrong literal type", KeYLexer.NUM_LITERAL == t ||
                KeYLexer.HEX_LITERAL == t ||
                KeYLexer.BIN_LITERAL == t ||
                KeYLexer.CHAR_LITERAL == t);
    }

    public Term parseTerm(String s) {
        KeyAst.Term ctx = ParsingFacade.parseExpression(CharStreams.fromString(s));
        return (Term) ctx.accept(new ExpressionBuilder(services, nss));
    }

    @Test
    public void testParse() {
        try {
            Term actual = parseTerm(input);
            if (type == ERROR) fail();
            else assertEquals(expected, actual.toString());
        } catch (Exception e) {
            if (type == ERROR)
                assertTrue("Wrong exception", e.getMessage().startsWith("Number constant out of bounds"));
            else throw e;
        }
    }
}
