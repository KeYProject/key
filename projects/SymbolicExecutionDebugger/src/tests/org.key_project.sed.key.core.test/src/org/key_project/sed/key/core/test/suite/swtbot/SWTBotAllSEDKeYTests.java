package org.key_project.sed.key.core.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYDebugTargetTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYModelThreadSaveChildAccessTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotLaunchDefaultPreferencesTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotMaximalNumberOfSetNodesPerBranchOnRunTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotStepOverTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotStepReturnTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotKeYDebugTargetTest.class,
   SWTBotKeYModelThreadSaveChildAccessTest.class,
   SWTBotLaunchDefaultPreferencesTest.class,
   SWTBotMaximalNumberOfSetNodesPerBranchOnRunTest.class,
   SWTBotStepOverTest.class,
   SWTBotStepReturnTest.class
})
public class SWTBotAllSEDKeYTests {
}
