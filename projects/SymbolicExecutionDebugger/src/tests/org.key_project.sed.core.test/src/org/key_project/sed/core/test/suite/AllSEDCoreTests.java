package org.key_project.sed.core.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.core.test.testcase.LogUtilTest;
import org.key_project.sed.core.test.testcase.SEDPostorderIteratorTest;
import org.key_project.sed.core.test.testcase.SEDPreferenceUtilInitializerTest;
import org.key_project.sed.core.test.testcase.SEDPreferenceUtilTest;
import org.key_project.sed.core.test.testcase.SEDPreorderIteratorTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   LogUtilTest.class,
   SEDPostorderIteratorTest.class,
   SEDPreferenceUtilInitializerTest.class,
   SEDPreferenceUtilTest.class,
   SEDPreorderIteratorTest.class
})
public class AllSEDCoreTests {
}
