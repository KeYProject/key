package org.key_project.util.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.util.test.testcase.swtbot.SWTBotLoggerTest;
import org.key_project.util.test.testcase.swtbot.SWTBotTableSelectionDialogTest;
import org.key_project.util.test.testcase.swtbot.SWTBotWorkbenchUtilTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    SWTBotLoggerTest.class,
    SWTBotTableSelectionDialogTest.class,
    SWTBotWorkbenchUtilTest.class
})
public class SWTBotAllUtilTests {
}
