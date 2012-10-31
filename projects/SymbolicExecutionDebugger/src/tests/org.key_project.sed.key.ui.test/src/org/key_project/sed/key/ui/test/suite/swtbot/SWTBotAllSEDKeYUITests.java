package org.key_project.sed.key.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotCustomizationTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotGraphitiCustomizationTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotGraphitiKeYTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotGraphitiMainTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotKeYSourceCodeLookupTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotKeYTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotMainTabTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotCustomizationTabTest.class,
   SWTBotGraphitiCustomizationTabTest.class,
   SWTBotGraphitiKeYTabTest.class,
   SWTBotGraphitiMainTabTest.class,
   SWTBotKeYSourceCodeLookupTest.class,
   SWTBotKeYTabTest.class,
   SWTBotMainTabTest.class
})
public class SWTBotAllSEDKeYUITests {
}
