package de.uka.ilkd.key.parser;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.util.HelperClassForTests;

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
        parseDecls("\\programVariables {Heap h;}");
        parseDecls("\\programVariables {testTermParserHeap.A a;}");
        parseDecls("\\programVariables {testTermParserHeap.A1 a1;}");
    }

    @Override
    protected Services getServices() {
        JavaInfo javaInfo = new HelperClassForTests().parse(
                new File(javaPath)).getFirstProof().getJavaInfo();
        return javaInfo.getServices();
    }

    public void testParsePrettyPrintedSelect() {
        Term t1, t2;

        t1 = parseTerm("a.f");
        t2 = parseTerm("int::select(heap, a, testTermParserHeap.A::$f)");
        assertEquals(t1, t2);

        t1 = parseTerm("a1.f");
        t2 = parseTerm("int::select(heap, a1, testTermParserHeap.A1::$f)");
        assertEquals(t1, t2);

        t1 = parseTerm("a1.(testTermParserHeap.A::f)");
        t2 = parseTerm("int::select(heap, a1, testTermParserHeap.A::$f)");
        assertEquals(t1, t2);
    }

    public void DISABLEDtestFieldAtHeapSyntax() {
        Term t1, t2;

        parseTerm("h");

        // test new syntax
        t1 = parseTerm("a.f@h");
        t2 = parseTerm("int::select(h, a, testTermParserHeap.A::$f)");
        assertEquals(t1, t2);

        t1 = parseTerm("a1.f@h");
        t2 = parseTerm("int::select(h, a1, testTermParserHeap.A1::$f)");
        assertEquals(t1, t2);

        t1 = parseTerm("a1.(A.f)@h");
        t2 = parseTerm("int::select(h, a1, A::$f)");
        assertEquals(t1, t2);
    }

    public void testStoreSyntax() {
//        parseTerm("heap[a.f := 4]");
    }

}
