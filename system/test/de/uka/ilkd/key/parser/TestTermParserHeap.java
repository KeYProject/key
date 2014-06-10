package de.uka.ilkd.key.parser;

import java.io.File;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.HelperClassForTests;

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
        String javaPath = System.getProperty("key.home") + "/system/proofExamples/_testcase/speclang/parserTest.key";
        JavaInfo javaInfo = new HelperClassForTests().parse(
                new File(javaPath)).getFirstProof().getJavaInfo();
        services = javaInfo.getServices();
        nss = services.getNamespaces();
//        TB = services.getTermBuilder();
        parseDecls("\\programVariables { testTermParserHeap.A a; }");
    }

    public void testTest() {
        // assert (services.getJavaInfo().getKeYJavaType("testTermParserHeap.A") != null);
    }

}
