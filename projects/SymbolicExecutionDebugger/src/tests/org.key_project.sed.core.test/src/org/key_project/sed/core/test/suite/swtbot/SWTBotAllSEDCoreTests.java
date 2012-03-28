package org.key_project.sed.core.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.core.test.testcase.swtbot.SWTBotDebugViewHierarchyTest;
import org.key_project.sed.core.test.testcase.swtbot.SWTBotSerializationTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotDebugViewHierarchyTest.class,
   SWTBotSerializationTest.class
})
public class SWTBotAllSEDCoreTests {
}
