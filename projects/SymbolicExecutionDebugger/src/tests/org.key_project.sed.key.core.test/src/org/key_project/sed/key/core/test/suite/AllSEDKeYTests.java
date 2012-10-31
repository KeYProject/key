package org.key_project.sed.key.core.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.core.test.testcase.ASTNodeByEndIndexSearcherTest;
import org.key_project.sed.key.core.test.testcase.KeYSourcePathComputerDelegateTest;
import org.key_project.sed.key.core.test.testcase.KeySEDUtilTest;
import org.key_project.sed.key.core.test.testcase.LogUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    ASTNodeByEndIndexSearcherTest.class,
    KeySEDUtilTest.class,
    KeYSourcePathComputerDelegateTest.class,
    LogUtilTest.class
})
public class AllSEDKeYTests {
}
