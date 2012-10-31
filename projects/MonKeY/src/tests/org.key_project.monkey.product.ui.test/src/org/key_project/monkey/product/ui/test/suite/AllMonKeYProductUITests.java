package org.key_project.monkey.product.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.monkey.product.ui.test.testcase.MonKeYBatchApplicationParametersTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    MonKeYBatchApplicationParametersTest.class
})
public class AllMonKeYProductUITests {
}
