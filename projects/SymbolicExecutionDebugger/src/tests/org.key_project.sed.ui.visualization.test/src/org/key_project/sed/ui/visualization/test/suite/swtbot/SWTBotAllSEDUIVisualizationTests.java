package org.key_project.sed.ui.visualization.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotGraphitiCallStackTabTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotGraphitiNodeTabTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotGraphitiSourceTabTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotGraphitiCallStackTabTest.class,
   SWTBotGraphitiNodeTabTest.class,
   SWTBotGraphitiSourceTabTest.class
})
public class SWTBotAllSEDUIVisualizationTests {
}
