package org.key_project.key4eclipse.util.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.util.test.testcase.swtbot.SWTBotLoggerTest;
import org.key_project.key4eclipse.util.test.testcase.swtbot.SWTBotWorkbenchUtilTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    SWTBotLoggerTest.class,
    SWTBotWorkbenchUtilTest.class
})
public class SWTBotAllUtilTests {
}
