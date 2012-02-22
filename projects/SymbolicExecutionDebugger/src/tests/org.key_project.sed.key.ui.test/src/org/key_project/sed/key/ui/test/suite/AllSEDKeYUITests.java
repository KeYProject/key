package org.key_project.sed.key.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.ui.test.testcase.AllOperationsSearchEngineTest;
import org.key_project.sed.key.ui.test.testcase.AllTypesSearchEngineTest;
import org.key_project.sed.key.ui.test.testcase.KeYSEDImagesTest;
import org.key_project.sed.key.ui.test.testcase.LogUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    AllOperationsSearchEngineTest.class,
    AllTypesSearchEngineTest.class,
    KeYSEDImagesTest.class,
    LogUtilTest.class
})
public class AllSEDKeYUITests {
}
