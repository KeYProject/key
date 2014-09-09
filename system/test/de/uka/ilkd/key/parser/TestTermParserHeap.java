package de.uka.ilkd.key.parser;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.util.HelperClassForTests;
import java.io.IOException;

/**
 * Parser tests for heap terms.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestTermParserHeap extends AbstractTestTermParser {

    private static final String javaPath = System.getProperty("key.home")
            + File.separator + "system"
            + File.separator + "proofExamples"
            + File.separator + "_testcase"
            + File.separator + "termParser"
            + File.separator + "parserTest.key";

    public TestTermParserHeap() {
        super(TestTermParserHeap.class.getSimpleName());
    }

    @Override
    public void setUp() {
        parseDecls("\\programVariables {Heap h, h2;}");
        parseDecls("\\programVariables {testTermParserHeap.A a;}");
        parseDecls("\\programVariables {testTermParserHeap.A1 a1;}");
    }

    @Override
    protected Services getServices() {
        JavaInfo javaInfo = new HelperClassForTests().parse(
                new File(javaPath)).getFirstProof().getJavaInfo();
        return javaInfo.getServices();
    }

    private Term getSelectTerm(String sort, Term heap, Term object, Term field) {
        Operator op = lookup_func(sort + "::select");
        Term[] params = new Term[]{heap, object, field};
        return tf.createTerm(op, params);
    }

    public void testParsePrettyPrintedSelect() throws IOException {
        String prettySyntax, verboseSyntax;

        prettySyntax = "a.f";
        verboseSyntax = "int::select(heap, a, testTermParserHeap.A::$f)";
        parsePrintAndCheckEquality(prettySyntax, verboseSyntax);

        prettySyntax = "a1.f";
        verboseSyntax = "int::select(heap, a1, testTermParserHeap.A1::$f)";
        parsePrintAndCheckEquality(prettySyntax, verboseSyntax);

        prettySyntax = "a1.(testTermParserHeap.A::f)";
        verboseSyntax = "int::select(heap, a1, testTermParserHeap.A::$f)";
        parsePrintAndCheckEquality(prettySyntax, verboseSyntax);
    }

    public void testBracketHeapUpdate() throws IOException {
        String prettySyntax = "heap[a.f := 4][create(a)][memset(empty, 1)][anon(allLocs, heap)]";
        String verboseSyntax = "anon(memset(create(store(heap, a, testTermParserHeap.A::$f, 4), a), empty, 1), allLocs, heap)";
//        parsePrintAndCheckEquality(prettySyntax, verboseSyntax);
        assertEquals(parseTerm(prettySyntax), parseTerm(verboseSyntax));
    }

    public void testFieldAtHeapSyntax() throws IOException {
        Term expectedParseResult, t2;
        String prettySyntax, verboseSyntax;

        prettySyntax = "a.f@h";
        verboseSyntax = "int::select(h, a, testTermParserHeap.A::$f)";
        parsePrintAndCheckEquality(prettySyntax, verboseSyntax);

        prettySyntax = "a1.f@h";
        verboseSyntax = "int::select(h, a1, testTermParserHeap.A1::$f)";
        parsePrintAndCheckEquality(prettySyntax, verboseSyntax);

        prettySyntax = "a1.(testTermParserHeap.A::f)@h";
        verboseSyntax = "int::select(h, a1, testTermParserHeap.A::$f)";
        parsePrintAndCheckEquality(prettySyntax, verboseSyntax);

        Term h = parseTerm("h");
        Term a = parseTerm("a");
        Term next = parseTerm("testTermParserHeap.A::$next");
        Term f = parseTerm("testTermParserHeap.A::$f");
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, a, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("int", h, expectedParseResult, f);
        parsePrintAndCheckEquality("a.next.next.next.f@h",
                expectedParseResult,
                "(a.next).next.next.f@h",
                "(a.next.next).next.f@h",
                "(a.next.next.next).f@h");

        Term h2 = parseTerm("h2");
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h2, a, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h2, expectedParseResult, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("int", h, expectedParseResult, f);

        t2 = parseTerm("(a.next.next@h2).next.f@h");
        assertEquals(expectedParseResult, t2);

        expectedParseResult = parseTerm("a.array[a.f]@h");

        Term x = getSelectTerm("int", tb.getBaseHeap(), a, f);
        Term idx = tb.arr(x);
        Term y = getSelectTerm("int[]", h, a, parseTerm("testTermParserHeap.A::$array"));
        Term z = getSelectTerm("int", h, y, idx);
        assertEquals(z, expectedParseResult);

        expectedParseResult = getSelectTerm("testTermParserHeap.A", tb.getBaseHeap(), a, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("int", h, expectedParseResult, f);
        t2 = parseTerm("(a.next@heap).next.f@h");
        assertEquals(expectedParseResult, t2);
        t2 = parseTerm("((a.next@heap)).next.f@h");
        assertEquals(expectedParseResult, t2);
    }

    public void testSyntax() {
        try {
            stringTermParser("(a.f + a.f)@h2").term();
            fail();
        } catch (Exception e) {
            assertTrue(e.getMessage().contains("Expecting select term before '@', not: "));
        }
    }

    /*
     * The following procedure is applied here:
     * 1) Take two plaintext inputs.
     * 2) Parse plaintexts and compare the results for equality.
     * 3) Pretty-print the one of the parsed plaintexts.
     * 4) Parse again and check if result did not change.
     */
    private void parsePrintAndCheckEquality(String prettySyntax, String verboseSyntax) throws IOException {
        Term expectedParseResult = parseTerm(verboseSyntax);
        parsePrintAndCheckEquality(prettySyntax, expectedParseResult);
    }

    private void parsePrintAndCheckEquality(String prettySyntax,
            Term expectedParseResult,
            String... optionalStringRepresentations) throws IOException {
        Term parsedPrettySyntax = parseTerm(prettySyntax);
        assertEquals(parsedPrettySyntax, expectedParseResult);

        LogicPrinter lp = new LogicPrinter(services);
        lp.printTerm(expectedParseResult);
        String printedSyntax = lp.toString();
        Term parsedPrintedSyntax = parseTerm(printedSyntax);
        assertEquals(parsedPrettySyntax, parsedPrintedSyntax);

        // compare the string representations, but remove whitespaces
        assertEquals(prettySyntax.replaceAll("\\s+", ""), printedSyntax.replaceAll("\\s+", ""));

        for (int i = 0; i < optionalStringRepresentations.length; i++) {
            assertEquals(parseTerm(optionalStringRepresentations[i]), expectedParseResult);
        }
    }

}
