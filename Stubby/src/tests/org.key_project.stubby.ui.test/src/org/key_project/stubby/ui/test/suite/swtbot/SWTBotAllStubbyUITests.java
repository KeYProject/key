package org.key_project.stubby.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.stubby.ui.test.testcase.swtbot.SWTBotGenerateStubsHandlerTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotGenerateStubsHandlerTest.class
})
public class SWTBotAllStubbyUITests {
}