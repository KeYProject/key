package org.key_project.sed.key.core.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.core.test.testcase.KeySEDUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    KeySEDUtilTest.class
})
public class AllSEDKeYTests {
}
