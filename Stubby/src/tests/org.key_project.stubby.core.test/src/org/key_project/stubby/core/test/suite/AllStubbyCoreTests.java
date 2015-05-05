package org.key_project.stubby.core.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.stubby.core.test.testcase.StubGeneratorUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   StubGeneratorUtilTest.class
})
public class AllStubbyCoreTests {
}