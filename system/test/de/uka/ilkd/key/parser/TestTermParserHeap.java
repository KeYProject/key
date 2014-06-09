package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.rule.TacletForTests;

/**
 * Parser tests for heap terms.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestTermParserHeap extends AbstractTestTermParser {

    public TestTermParserHeap() {
        super(TestTermParserHeap.class.getSimpleName());
    }

    @Override
    public void setUpDeclarations() {
        String javaPath = System.getProperty("key.home") + "/system/proofExamples/_testcase/speclang/testTermParserHeap/A.java";
        TacletForTests.parse(javaPath);
        parseDecls("\\programVariables { A a; }");
    }

    public void testTest() {
        assert (services.getJavaInfo().getKeYJavaType("testTermParserHeap.A") != null);
    }

}
