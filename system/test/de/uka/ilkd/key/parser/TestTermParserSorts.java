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
        parseDecls("\\programVariables {"
                + "testTermParserSorts.IntegerMethods a;"
                + "byte[] ba;"
                + "char[] ca;"
                + "short[] sa;"
                + "int[] ia;"
                + "long[] la;"
                + "}");
    }

    /*
     * Test whether pretty syntax of sequences is parsed correctly.
     */
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

    /*
     * The KeY type int has several possible corresponding KeYJavaTypes.
     * Those types are: char, byte, short, int, long
     * 
     * This test checks if the parser finds a suitable function,
     * if a query with integer arguments is provided.
     *
     * Sometimes several functions are available that the parser may select.
     * For example a query of the form "a.query(0)" with Java functions
     * available that have the following signatures:
     *
     *      public int query(int i);
     *      public int query(byte b);
     *
     * Such a case is not considered here.
     */
    public void testParseIntegerArgs() throws Exception {
        String s = "testTermParserSorts.IntegerMethods::queryByte(heap,a,Z(0(#)))";
        Term t = parseTerm("a.queryByte(0)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryByteArray(heap,a,ba)";
        t = parseTerm("a.queryByteArray(ba)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryChar(heap,a,Z(0(#)))";
        t = parseTerm("a.queryChar(0)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryCharArray(heap,a,ca)";
        t = parseTerm("a.queryCharArray(ca)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryShort(heap,a,Z(0(#)))";
        t = parseTerm("a.queryShort(0)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryShortArray(heap,a,sa)";
        t = parseTerm("a.queryShortArray(sa)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryInt(heap,a,Z(0(#)))";
        t = parseTerm("a.queryInt(0)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryIntArray(heap,a,ia)";
        t = parseTerm("a.queryIntArray(ia)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryLong(heap,a,Z(0(#)))";
        t = parseTerm("a.queryLong(0)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryLongArray(heap,a,la)";
        t = parseTerm("a.queryLongArray(la)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryMixed(heap,a,Z(0(#)),ca,Z(0(#)),ia,Z(0(#)))";
        t = parseTerm("a.queryMixed(0,ca,0,ia,0)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryMixedStatic(heap,Z(0(#)),ca,Z(0(#)),ia,Z(0(#)))";
        t = parseTerm("a.queryMixedStatic(0,ca,0,ia,0)");
        assertEquals(s, t.toString());

        s = "testTermParserSorts.IntegerMethods::queryMixedStatic(heap,Z(0(#)),ca,Z(0(#)),ia,Z(0(#)))";
        t = parseTerm("testTermParserSorts.IntegerMethods.queryMixedStatic(0,ca,0,ia,0)");
        assertEquals(s, t.toString());
    }

}
