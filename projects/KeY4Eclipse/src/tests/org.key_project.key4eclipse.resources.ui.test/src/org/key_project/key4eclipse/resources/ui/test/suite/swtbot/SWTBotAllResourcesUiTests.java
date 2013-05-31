package org.key_project.key4eclipse.resources.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.resources.ui.test.testcase.swtbot.SWTBotConvertToKeYProjectTest;
import org.key_project.key4eclipse.resources.ui.test.testcase.swtbot.SWTBotKeYProjectWizardTest;

@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotKeYProjectWizardTest.class,
   SWTBotConvertToKeYProjectTest.class
})
public class SWTBotAllResourcesUiTests {

}
