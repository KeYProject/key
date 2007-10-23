package de.uka.ilkd.key.util.removegenerics;

import junit.framework.Test;
import junit.framework.TestSuite;

public class AllTests {

    public static Test suite() {
        TestSuite suite = new TestSuite("Test for de.uka.ilkd.key.tools");
        //$JUnit-BEGIN$
        suite.addTestSuite(TestMultipleBounds.class);
        suite.addTestSuite(TestTypeReference.class);
        suite.addTestSuite(TestMemberReference.class);
        suite.addTestSuite(TestMethodDeclaration.class);
        suite.addTestSuite(TestClassDeclaration.class);
        //$JUnit-END$
        return suite;
    }

}
