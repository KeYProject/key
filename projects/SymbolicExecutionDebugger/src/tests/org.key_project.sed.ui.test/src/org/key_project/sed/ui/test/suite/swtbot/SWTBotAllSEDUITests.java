package org.key_project.sed.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.ui.test.testcase.swtbot.SWTBotCallStackTabTest;
import org.key_project.sed.ui.test.testcase.swtbot.SWTBotNodeTabTest;
import org.key_project.sed.ui.test.testcase.swtbot.SWTBotSourceTabTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    SWTBotCallStackTabTest.class,
    SWTBotNodeTabTest.class,
    SWTBotSourceTabTest.class
})
public class SWTBotAllSEDUITests {
}
