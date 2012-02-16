package org.key_project.key4eclipse.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.test.testcase.KeYExampleUtilTest;
import org.key_project.key4eclipse.test.testcase.MainTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   KeYExampleUtilTest.class,
   MainTest.class
   //RunAllProofsTest.class // This class is not listed because it takes to much time.
})
public class AllKeY4EclipseTests {
}
