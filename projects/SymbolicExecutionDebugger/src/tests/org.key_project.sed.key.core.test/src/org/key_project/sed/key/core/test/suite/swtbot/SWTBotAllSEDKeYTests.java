package org.key_project.sed.key.core.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYDebugTargetTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotKeYDebugTargetTest.class
})
public class SWTBotAllSEDKeYTests {
}
