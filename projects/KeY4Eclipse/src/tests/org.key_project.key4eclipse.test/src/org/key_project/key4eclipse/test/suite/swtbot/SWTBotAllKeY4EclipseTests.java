package org.key_project.key4eclipse.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.test.testcase.swtbot.SWTBotExampleTest;
import org.key_project.key4eclipse.test.testcase.swtbot.SWTBotMainTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    SWTBotExampleTest.class,
    SWTBotMainTest.class
})
public class SWTBotAllKeY4EclipseTests {
}
