package org.key_project.keyide.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.keyide.ui.test.testcase.swtbot.SWTBotStartProofHandlerTest;

/**
 * <p>
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * </p>
 * <p>
 * Requires the following JVM settings: -Xms128m -Xmx1024m -XX:MaxPermSize=256m
 * </p>
 * <p>
 * If you got timeout exceptions increase the waiting time with the following
 * additional JVM parameter: -Dorg.eclipse.swtbot.search.timeout=10000
 * </p>
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   // TODO: Add SWTBotAutoModeHandlerTest.class and all other new SWTBot test classes in the future!
   SWTBotStartProofHandlerTest.class
})
public class SWTBotAllKeYIDEUITests {
}
