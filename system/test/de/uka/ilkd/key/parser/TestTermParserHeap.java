package de.uka.ilkd.key.parser;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import static de.uka.ilkd.key.parser.KeYParserF.noHeapExpressionBeforeAtExceptionMessage;
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
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        prettySyntax = "a1.f";
        verboseSyntax = "int::select(heap, a1, testTermParserHeap.A1::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        prettySyntax = "a1.(testTermParserHeap.A::f)";
        verboseSyntax = "int::select(heap, a1, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    public void testBracketHeapUpdate() throws IOException {
        String prettySyntax = "heap[a.f := 4][create(a)][memset(empty, 1)][anon(allLocs, heap)]";
        String verboseSyntax = "anon(memset(create(store(heap, a, testTermParserHeap.A::$f, 4), a), empty, 1), allLocs, heap)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    /*
     * The @-Operator can be used to specify the heap, which belongs to a
     * field access. That operator is tests in the method below.
     */
    public void testAtOperator() throws IOException {
        Term expectedParseResult;
        String prettySyntax, verboseSyntax;

        prettySyntax = "a.f@h";
        verboseSyntax = "int::select(h, a, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        prettySyntax = "a1.f@h";
        verboseSyntax = "int::select(h, a1, testTermParserHeap.A1::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        prettySyntax = "a1.(testTermParserHeap.A::f)@h";
        verboseSyntax = "int::select(h, a1, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        Term h = parseTerm("h");
        Term a = parseTerm("a");
        Term next = parseTerm("testTermParserHeap.A::$next");
        Term f = parseTerm("testTermParserHeap.A::$f");
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, a, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("int", h, expectedParseResult, f);
        compareStringRepresentationAgainstTermRepresentation("a.next.next.next.f@h",
                expectedParseResult,
                "(a.next).next.next.f@h",
                "(a.next.next).next.f@h",
                "(a.next.next.next).f@h");

        Term h2 = parseTerm("h2");
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h2, a, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h2, expectedParseResult, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("int", h, expectedParseResult, f);
        compareStringRepresentationAgainstTermRepresentation("(a.next.next@h2).next.f@h", expectedParseResult);

        Term aDotF = getSelectTerm("int", tb.getBaseHeap(), a, f); // a.f
        Term aDotArray = getSelectTerm("int[]", h, a, parseTerm("testTermParserHeap.A::$array")); // a.array
        expectedParseResult = getSelectTerm("int", h, aDotArray, tb.arr(aDotF));
        compareStringRepresentationAgainstTermRepresentation("a.array[a.f]@h", expectedParseResult);

        expectedParseResult = getSelectTerm("testTermParserHeap.A", tb.getBaseHeap(), a, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("int", h, expectedParseResult, f);
        compareStringRepresentationAgainstTermRepresentation("(a.next@heap).next.f@h",
                expectedParseResult,
                "((a.next@heap)).next.f@h");
    }

    /*
     * In this test, the @-Operator is applied on a non-select term.
     * This should cause a parser error. This test verifies that the correct
     * Exception is thrown.
     */
    public void testVerifyExceptionIfAtOperatorNotPreceededBySelectTerm() {
        try {
            stringTermParser("(a.f + a.f)@h2").term();
            fail();
        } catch (Exception e) {
            assertTrue(e.getMessage().contains(noHeapExpressionBeforeAtExceptionMessage));
        }
    }

    public void testQuantifiedSelect() throws IOException {
        Term t = parseFormula("\\forall Object o; \\forall Field f; o.f = 1");
//        String s = printTerm(t);
//        System.out.println(s);
//        String verboseSyntax = "\\forall Field f; any::select(heap,a,f) = int::select(heap,a,testTermParserHeap.A::$f)";
//        String prettySyntax = "\\forall Field f; any::select(heap, a, f) = a.f";
//        parsePrintAndCheckEquality(prettySyntax, verboseSyntax);
//        Term t = parseTerm("\\forall Field f; any::select(heap,a,f) = a.f");
//        System.out.println(t);
//        System.out.println(printTerm(t));
    }

    public void testGenericObjectProperties() throws IOException {
        // test pretty syntax
        comparePrettySyntaxAgainstVerboseSyntax("a.<created>", "boolean::select(heap,a,java.lang.Object::<created>)");
        comparePrettySyntaxAgainstVerboseSyntax("a.<initialized>", "boolean::select(heap,a,java.lang.Object::<initialized>)");
        comparePrettySyntaxAgainstVerboseSyntax("a.<transient>", "int::select(heap,a,java.lang.Object::<transient>)");

        // test fallback mode in case non-default select-type is used
        parseAndPrint("int::select(heap,a,java.lang.Object::<created>)");

    }

    /**
     * Remove whitespaces before executing
     * {@link junit.framework.TestCase#assertEquals(java.lang.String, java.lang.String)}.
     */
    private void assertEqualsIgnoreWhitespaces(String expected, String actual) {
        assertEquals(expected.replaceAll("\\s+", ""), actual.replaceAll("\\s+", ""));
    }

    /**
     * Convert a {@link Term} into a {@link String}.
     *
     * @param t The {@link Term} that will be converted.
     */
    private String printTerm(Term t) throws IOException {
        LogicPrinter lp = new LogicPrinter(services);
        lp.printTerm(t);
        return lp.toString();
    }

    /**
     * Test whether printing is inverse to parsing on a specific {@link String}.
     *
     * @param s Pretty-printed String representation of a term.
     * @throws IOException
     */
    private void parseAndPrint(String s) throws IOException {
        Term t = parseTerm(s);
        String printedSyntax = printTerm(t);
        assertEqualsIgnoreWhitespaces(s, printedSyntax);
    }

    /**
     * Takes two different String representations for the same term and checks
     * whether they result in the same {@link Term} after parsing. Subsequently,
     * the {@link Term} is printed back to a {@link String} and compared with
     * the first argument. The first argument is expected to be in
     * pretty-syntax.
     *
     * @param prettySyntax {@link Term} representation in pretty-syntax.
     * @param verboseSyntax {@link Term} in verbose syntax.
     * @throws IOException
     */
    private void comparePrettySyntaxAgainstVerboseSyntax(String prettySyntax, String verboseSyntax) throws IOException {
        Term expectedParseResult = parseTerm(verboseSyntax);
        compareStringRepresentationAgainstTermRepresentation(prettySyntax, expectedParseResult);
    }

    /**
     * Takes a {@link String} and a {@link Term} and checks whether they can be
     * transformed into each other by the operations parsing and printing.
     *
     * @param expectedPrettySyntax Expected result after pretty-printing
     * {@code expectedParseResult}.
     * @param expectedParseResult Expected result after parsing
     * {@code expectedPrettySyntax}.
     * @param optionalStringRepresentations Optionally, additional String
     * representations will be tested for correct parsing.
     * @throws IOException
     */
    private void compareStringRepresentationAgainstTermRepresentation(String expectedPrettySyntax, Term expectedParseResult,
            String... optionalStringRepresentations) throws IOException {
        Term parsedPrettySyntax = parseTerm(expectedPrettySyntax);
        assertEquals(expectedParseResult, parsedPrettySyntax);

        String printedSyntax = printTerm(expectedParseResult);
        // compare the string representations, but remove whitespaces
        assertEqualsIgnoreWhitespaces(expectedPrettySyntax, printedSyntax);

        // parse printed term again and see if result is still the same
        Term parsedPrintedSyntax = parseTerm(printedSyntax);
        assertEquals(expectedParseResult, parsedPrintedSyntax);

        /*
         * Optionally, further string representations of the same term will be parsed here.
         */
        for (int i = 0; i < optionalStringRepresentations.length; i++) {
            assertEquals(expectedParseResult, parseTerm(optionalStringRepresentations[i]));
        }
    }

}
