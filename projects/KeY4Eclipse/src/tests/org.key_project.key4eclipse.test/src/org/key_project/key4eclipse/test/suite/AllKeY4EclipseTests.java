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
})
public class AllKeY4EclipseTests {
}
