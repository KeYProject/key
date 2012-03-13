package org.key_project.sed.key.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotKeYSourceCodeLookupTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotKeYSourceCodeLookupTest.class
})
public class SWTBotAllSEDKeYUITests {
}
