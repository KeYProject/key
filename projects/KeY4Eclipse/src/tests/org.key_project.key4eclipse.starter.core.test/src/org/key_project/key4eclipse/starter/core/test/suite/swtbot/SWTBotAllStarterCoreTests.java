package org.key_project.key4eclipse.starter.core.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.starter.core.test.testcase.swtbot.SWTBotKeYUtilTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    SWTBotKeYUtilTest.class
})
public class SWTBotAllStarterCoreTests {
}
