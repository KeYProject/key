package org.key_project.removegenerics.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.removegenerics.ui.test.testcase.swtbot.SWTBotRemoveGenericsTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotRemoveGenericsTest.class
})
public class SWTBotAllRemoveGenericsUITests {
}