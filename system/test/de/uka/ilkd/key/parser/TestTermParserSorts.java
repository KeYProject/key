package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.logic.Term;
import org.antlr.runtime.RecognitionException;

/**
 * Testing pretty-printing and parsing of seqGet terms in this class.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestTermParserSorts extends AbstractTestTermParser {

    public TestTermParserSorts() {
        super(TestTermParserSorts.class.getSimpleName());
    }

    @Override
    public void setUp() throws RecognitionException {
        parseDecls("\\programVariables {Seq s;}");
        parseDecls("\\programVariables {int i;}");
        parseDecls("\\programVariables {testTermParserSorts.IntegerMethods a;}");
    }

    public void testParseSequencePrettySyntax() throws Exception {
        /*
         * Test any::seqGet(s,i)
         */
        String pp = "s[i]";
        Term expected = parseTerm("any::seqGet(s,i)");
        Term actual = parseTerm(pp);
        assertEquals(expected, actual); // test parsing
        assertEqualsIgnoreWhitespaces(printTerm(expected), pp); // test pretty-printing

        /*
         * Test int::seqGet(s,i)
         * Notice that pretty-printing of int::seqGet(s,i) results in: (int)s[i]
         * But parsing of (int)s[i] results in: int::cast(any::seqGet(s,i)
         */
        pp = "(int)s[i]";
        expected = parseTerm("int::cast(any::seqGet(s,i))");
        actual = parseTerm(pp);
        assertEquals(expected, actual); // test parsing
        assertEqualsIgnoreWhitespaces(printTerm(parseTerm("int::seqGet(s,i)")), pp); // test pretty-printing

        // test parsing of pretty-printed seqLen
        comparePrettySyntaxAgainstVerboseSyntax("s.length", "seqLen(s)");
    }

    public void testParseIntegerArgs() throws Exception {
//        System.out.println(parseTerm("a.queryByte(0)"));
//        System.out.println(parseTerm("a.queryChar(0)"));
//        System.out.println(parseTerm("a.queryShort(0)"));
//        System.out.println(parseTerm("a.queryInt(0)"));
//        System.out.println(parseTerm("a.queryLong(0)"));
//        System.out.println(parseTerm("a.queryMixed(0,0,0,0,0)"));
//        System.out.println(parseTerm("a.queryMixedStatic(0,0,0,0,0)"));
//        System.out.println(parseTerm("testTermParserSorts.IntegerMethods.queryMixedStatic(0,0,0,0,0)"));
    }

}
