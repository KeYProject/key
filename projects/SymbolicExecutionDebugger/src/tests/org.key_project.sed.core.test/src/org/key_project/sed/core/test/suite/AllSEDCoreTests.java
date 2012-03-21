package org.key_project.sed.core.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.core.test.testcase.SEDPreferenceUtilInitializerTest;
import org.key_project.sed.core.test.testcase.SEDPreferenceUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SEDPreferenceUtilInitializerTest.class,
   SEDPreferenceUtilTest.class
})
public class AllSEDCoreTests {
}
