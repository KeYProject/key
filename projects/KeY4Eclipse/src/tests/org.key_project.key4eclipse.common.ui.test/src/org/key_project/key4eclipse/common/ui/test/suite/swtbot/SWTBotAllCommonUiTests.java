package org.key_project.key4eclipse.common.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.common.ui.test.testcase.swtbot.SWTBotTacletOptionsPreferencePageTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotTacletOptionsPreferencePageTest.class
})
public class SWTBotAllCommonUiTests {
}
