package de.uka.ilkd.key.parser;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import static de.uka.ilkd.key.parser.KeYParserF.NO_HEAP_EXPRESSION_BEFORE_AT_EXCEPTION_MESSAGE;
import de.uka.ilkd.key.util.HelperClassForTests;
import java.io.IOException;

/**
 * Parser tests for heap terms.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestTermParserHeap extends AbstractTestTermParser {

    static final String javaPath = System.getProperty("key.home")
            + File.separator + "examples"
            + File.separator + "_testcase"
            + File.separator + "termParser"
            + File.separator + "parserTest.key";

    public TestTermParserHeap() {
        super(TestTermParserHeap.class.getSimpleName());
    }

    @Override
    public void setUp() {
        parseDecls("\\programVariables {Heap h, h2;}");
        parseDecls("\\programVariables {int i;}");
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

    public void testLocationSets() throws IOException {
        comparePrettySyntaxAgainstVerboseSyntax(
                "{(a, testTermParserHeap.A::$f)}",
                "singleton(a,testTermParserHeap.A::$f)");
    }

    public void testParsePrettyPrintedSelect() throws IOException {
        String prettySyntax = "a.f";
        String verboseSyntax = "int::select(heap, a, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        prettySyntax = "a1.f";
        verboseSyntax = "int::select(heap, a1, testTermParserHeap.A1::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        prettySyntax = "a1.(testTermParserHeap.A::f)";
        verboseSyntax = "int::select(heap, a1, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    public void testBracketHeapUpdate() throws IOException {
        String complicatedHeapPretty = "heap[a.f := 4][create(a)][memset(empty, 1)][anon(allLocs, heap)]";
        String complicatedHeapVerbose = "anon(memset(create(store(heap, a, testTermParserHeap.A::$f, 4), a), empty, 1), allLocs, heap)";
        comparePrettySyntaxAgainstVerboseSyntax(complicatedHeapPretty, complicatedHeapVerbose);

        String prettySyntax = "a.f@h[anon(empty, h2)]";
        String verboseSyntax = "int::select(anon(h, empty, h2), a, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        /*
         * Testing a more complicated term in which bracket syntax is applied
         * before and after @-Operator.
         */
        prettySyntax = "a.next.next.array[i]@" + complicatedHeapPretty;
        verboseSyntax = "int::select(" + complicatedHeapVerbose + ", "
                + "int[]::select(" + complicatedHeapVerbose + ", "
                + "testTermParserHeap.A::select(" + complicatedHeapVerbose + ", "
                + "testTermParserHeap.A::select(" + complicatedHeapVerbose + ", "
                + " a, testTermParserHeap.A::$next)"
                + ", testTermParserHeap.A::$next)"
                + ", testTermParserHeap.A::$array)"
                + ", arr(i))";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    /*
     * The @-Operator can be used to specify the heap, which belongs to a
     * field access. That operator is tested in the method below.
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

        aDotF = getSelectTerm("int", h, a, f); // a.f
        aDotArray = getSelectTerm("int[]", tb.getBaseHeap(), a, parseTerm("testTermParserHeap.A::$array")); // a.array
        expectedParseResult = getSelectTerm("int", tb.getBaseHeap(), aDotArray, tb.arr(aDotF));
        compareStringRepresentationAgainstTermRepresentation("a.array[a.f@h]", expectedParseResult);

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
            getParser("(a.f + a.f)@h2").term();
            fail();
        } catch (Exception e) {
            assertTrue(e.getMessage().contains(NO_HEAP_EXPRESSION_BEFORE_AT_EXCEPTION_MESSAGE));
        }
    }

    public void testQuantifiedSelect() throws IOException {
        String quantification = "\\forall java.lang.Object o; \\forall Field f; o.f = 1";
        String expectedToString = "all{o:java.lang.Object}(all{f:Field}(equals(any::select(heap,o,f),Z(1(#)))))";
        comparePrettyPrintAgainstToString(quantification, expectedToString);

        quantification = "\\forall Field f; a.f = any::select(heap, a, f)";
        expectedToString = "all{f:Field}(equals(int::select(heap,a,testTermParserHeap.A::$f),any::select(heap,a,f)))";
        comparePrettyPrintAgainstToString(quantification, expectedToString);

    }

    private void comparePrettyPrintAgainstToString(String quantification, String expectedToString) throws IOException {
        Term t = parseTerm(quantification);
        assertEquals(expectedToString, t.toString());
        assertEqualsIgnoreWhitespaces(quantification, printTerm(t));
    }

    public void testGenericObjectProperties() throws IOException {
        // test pretty syntax
        comparePrettySyntaxAgainstVerboseSyntax("a.<created>", "boolean::select(heap,a,java.lang.Object::<created>)");
        comparePrettySyntaxAgainstVerboseSyntax("a.<initialized>", "boolean::select(heap,a,java.lang.Object::<initialized>)");
        comparePrettySyntaxAgainstVerboseSyntax("a.<transient>", "int::select(heap,a,java.lang.Object::<transient>)");

        // test fallback mode in case non-default select-type is used
        parseAndPrint("int::select(heap,a,java.lang.Object::<created>)");

    }

    public void testQueries() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("a.query(i)", "testTermParserHeap.A::query(heap, a, i)");
        comparePrettySyntaxAgainstVerboseSyntax("a.query(i)@h", "testTermParserHeap.A::query(h, a, i)");
        comparePrettySyntaxAgainstVerboseSyntax("a.query(a.f)@h", "testTermParserHeap.A::query(h, a, "
                + "int::select(heap, a, testTermParserHeap.A::$f))");

        comparePrettySyntaxAgainstVerboseSyntax("a.next.query(a.f)@h", "testTermParserHeap.A::query(h, "
                + "testTermParserHeap.A::select(h, a, testTermParserHeap.A::$next),  "
                + "int::select(heap, a, testTermParserHeap.A::$f))");

        comparePrettySyntaxAgainstVerboseSyntax("a.getNext().getNext()@h", "testTermParserHeap.A::getNext(h, "
                + "testTermParserHeap.A::getNext(h, a))");

        comparePrettySyntaxAgainstVerboseSyntax("a.getNext().next@h", "testTermParserHeap.A::select(h, "
                + "testTermParserHeap.A::getNext(h, a), testTermParserHeap.A::$next)");

        comparePrettySyntaxAgainstVerboseSyntax("(a.getNext()@h2).next@h", "testTermParserHeap.A::select(h, "
                + "testTermParserHeap.A::getNext(h2, a), testTermParserHeap.A::$next)");

        comparePrettySyntaxAgainstVerboseSyntax("(a.getNext()@heap).next@h", "testTermParserHeap.A::select(h, "
                + "testTermParserHeap.A::getNext(heap, a), testTermParserHeap.A::$next)");

        comparePrettySyntaxAgainstVerboseSyntax("(a.next@heap).getNext()@h", "testTermParserHeap.A::getNext(h, "
                + "testTermParserHeap.A::select(heap, a, testTermParserHeap.A::$next))");
    }

    public void testQueriesInheritance() throws Exception {
        compareStringRepresentationAgainstTermRepresentation("a.query(i)",
                parseTerm("testTermParserHeap.A::query(heap, a, i)"),
                "a.(testTermParserHeap.A::query)(i)");

        compareStringRepresentationAgainstTermRepresentation("a1.query(i)",
                parseTerm("testTermParserHeap.A::query(heap, a1, i)"),
                "a1.(testTermParserHeap.A::query)(i)");

        compareStringRepresentationAgainstTermRepresentation("a1.queryRedefined()",
                parseTerm("testTermParserHeap.A1::queryRedefined(heap, a1)"),
                "a1.(testTermParserHeap.A1::queryRedefined)()");

//        compareStringRepresentationAgainstTermRepresentation("a1.(testTermParserHeap.A::queryRedefined)()",
//                parseTerm("testTermParserHeap.A::queryRedefined(heap, a1)"));
//        compareStringRepresentationAgainstTermRepresentation("a1.queryOverridden()",
//                parseTerm("testTermParserHeap.A::queryOverridden(heap, a1)"));
    }

    /*
     * Test pretty-printing on static fields and methods.
     */
    public void testAccessStaticMembers() throws IOException {
        // static field access
        comparePrettySyntaxAgainstVerboseSyntax("testTermParserHeap.A.staticField",
                "int::select(heap, null, testTermParserHeap.A::$staticField)");

        // static method access
        comparePrettySyntaxAgainstVerboseSyntax("testTermParserHeap.A.staticMethod()",
                "testTermParserHeap.A::staticMethod(heap)");

        // static array access
        comparePrettySyntaxAgainstVerboseSyntax("testTermParserHeap.A.staticArray[0]",
                "int::select(heap,int[]::select(heap,null,testTermParserHeap.A::$staticArray),arr(Z(0(#))))");
    }

    /*
     * Test parsing and printing of store-terms.
     */
    public void testStore() throws IOException {
        String pretty, verbose;

        // non-static non-hidden field
        pretty = "heap[a.f := null]";
        verbose = "store(heap, a, testTermParserHeap.A::$f, null)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

        // non-static hidden field
        pretty = "heap[a.(testTermParserHeap.A1::f) := null]";
        verbose = "store(heap, a, testTermParserHeap.A1::$f, null)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

        // static field
        pretty = "heap[testTermParserHeap.A.staticArray := null]";
        verbose = "store(heap, null, testTermParserHeap.A::$staticArray, null)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

        // element of static array
        pretty = "heap[testTermParserHeap.A.staticArray[i] := i]";
        verbose = "store(heap, int[]::select(heap,null,testTermParserHeap.A::$staticArray), arr(i), i)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

        // object property
        pretty = "heap[create(a)][a.<initialized> := FALSE]";
        verbose = "store(create(heap,a),a,java.lang.Object::<initialized>,FALSE)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

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
    private void comparePrettySyntaxAgainstVerboseSyntax(String prettySyntax, String verboseSyntax,
            String... optionalStringRepresentations) throws IOException {
        Term expectedParseResult = parseTerm(verboseSyntax);
        compareStringRepresentationAgainstTermRepresentation(prettySyntax, expectedParseResult, optionalStringRepresentations);
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
