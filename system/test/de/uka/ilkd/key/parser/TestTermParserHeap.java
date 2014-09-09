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
        String s1 = "heap[a.f := 4][create(a)][memset(empty, 1)][anon(allLocs, heap)]";
        String s2 = "anon(memset(create(store(heap, a, testTermParserHeap.A::$f, 4), a), empty, 1), allLocs, heap)";
//        parsePrintAndCheckEquality(s1, s2);
        assertEquals(parseTerm(s1), parseTerm(s2));
    }

    public void testFieldAtHeapSyntax() {
        Term t1, t2;

        t1 = parseTerm("a.f@h");
        t2 = parseTerm("int::select(h, a, testTermParserHeap.A::$f)");
        assertEquals(t1, t2);

        t1 = parseTerm("a1.f@h");
        t2 = parseTerm("int::select(h, a1, testTermParserHeap.A1::$f)");
        assertEquals(t1, t2);

        t1 = parseTerm("a1.(testTermParserHeap.A::f)@h");
        t2 = parseTerm("int::select(h, a1, testTermParserHeap.A::$f)");
        assertEquals(t1, t2);

        Term h = parseTerm("h");
        Term a = parseTerm("a");
        Term next = parseTerm("testTermParserHeap.A::$next");
        Term f = parseTerm("testTermParserHeap.A::$f");
        t1 = getSelectTerm("testTermParserHeap.A", h, a, next);
        t1 = getSelectTerm("testTermParserHeap.A", h, t1, next);
        t1 = getSelectTerm("testTermParserHeap.A", h, t1, next);
        t1 = getSelectTerm("int", h, t1, f);

        t2 = parseTerm("a.next.next.next.f@h");
        assertEquals(t1, t2);

        t2 = parseTerm("(a.next).next.next.f@h");
        assertEquals(t1, t2);

        t2 = parseTerm("(a.next.next).next.f@h");
        assertEquals(t1, t2);

        t2 = parseTerm("(a.next.next.next).f@h");
        assertEquals(t1, t2);

        Term h2 = parseTerm("h2");
        t1 = getSelectTerm("testTermParserHeap.A", h2, a, next);
        t1 = getSelectTerm("testTermParserHeap.A", h2, t1, next);
        t1 = getSelectTerm("testTermParserHeap.A", h, t1, next);
        t1 = getSelectTerm("int", h, t1, f);

        t2 = parseTerm("(a.next.next@h2).next.f@h");
        assertEquals(t1, t2);

        t1 = parseTerm("a.array[a.f]@h");

        Term x = getSelectTerm("int", tb.getBaseHeap(), a, f);
        Term idx = tb.arr(x);
        Term y = getSelectTerm("int[]", h, a, parseTerm("testTermParserHeap.A::$array"));
        Term z = getSelectTerm("int", h, y, idx);
        assertEquals(z, t1);

        t1 = getSelectTerm("testTermParserHeap.A", tb.getBaseHeap(), a, next);
        t1 = getSelectTerm("testTermParserHeap.A", h, t1, next);
        t1 = getSelectTerm("int", h, t1, f);
        t2 = parseTerm("(a.next@heap).next.f@h");
        assertEquals(t1, t2);
        t2 = parseTerm("((a.next@heap)).next.f@h");
        assertEquals(t1, t2);
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
    public void parsePrintAndCheckEquality(String prettySyntax, String verboseSyntax) throws IOException {
        Term t1 = parseTerm(prettySyntax);
        Term t2 = parseTerm(verboseSyntax);
        assertEquals(t1, t2);

        LogicPrinter lp = new LogicPrinter(services);
        lp.printTerm(t2);
        String printedSyntax = lp.toString();
        Term t3 = parseTerm(printedSyntax);
        assertEquals(t1, t3);
        
        // compare the string representations, but remove whitespaces
        assertEquals(prettySyntax.replaceAll("\\s+",""), printedSyntax.replaceAll("\\s+",""));
    }

}
