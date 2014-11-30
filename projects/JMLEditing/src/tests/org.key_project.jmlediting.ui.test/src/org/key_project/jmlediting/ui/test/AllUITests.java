package org.key_project.jmlediting.ui.test;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.ui.test.extension.JMLLocatorTest;
import org.key_project.jmlediting.ui.test.suite.CompletionSuite;
import org.key_project.jmlediting.ui.test.suite.PreferenceSuite;

@RunWith(Suite.class)
@SuiteClasses({ CompletionSuite.class, JMLLocatorTest.class,
      PreferenceSuite.class })
public class AllUITests {

}
