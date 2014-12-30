package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.logic.Term;
import org.antlr.runtime.RecognitionException;

/**
 * Testing pretty-printing and parsing of seqGet terms in this class.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestTermParserSequence extends AbstractTestTermParser {

    public TestTermParserSequence() {
        super(TestTermParserSequence.class.getSimpleName());
    }

    @Override
    public void setUp() throws RecognitionException {
        parseDecls("\\programVariables {Seq s;}");
        parseDecls("\\programVariables {int i;}");
    }

    public void testParsePrettySyntax() throws Exception {
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

}
