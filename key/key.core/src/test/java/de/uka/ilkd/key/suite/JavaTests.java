package de.uka.ilkd.key.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
        de.uka.ilkd.key.java.TestJavaInfo.class,
        de.uka.ilkd.key.java.TestJavaCardDLJavaExtensions.class,
        de.uka.ilkd.key.java.TestRecoder2KeY.class,
        de.uka.ilkd.key.java.TestKeYRecoderMapping.class,
        de.uka.ilkd.key.java.visitor.TestDeclarationProgramVariableCollector.class,
        de.uka.ilkd.key.java.TestContextStatementBlock.class
})
public class JavaTests {
}