package de.uka.ilkd.key.parser;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
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
        parseDecls("\\schemaVariables {\\term Heap h;}");
        parseDecls("\\programVariables { testTermParserHeap.A a; }");
    }

    @Override
    protected Services getServices() {
        JavaInfo javaInfo = new HelperClassForTests().parse(
                new File(javaPath)).getFirstProof().getJavaInfo();
        return javaInfo.getServices();
    }

    public void testAtHeapSyntax() {
        parseTerm("h");
        parseTerm("a.f");
        parseTerm("a.f@h");
    }

}
