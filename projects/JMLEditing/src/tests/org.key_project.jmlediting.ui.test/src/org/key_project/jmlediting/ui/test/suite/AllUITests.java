package org.key_project.jmlediting.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmledeting.ui.test.hover.JMLHoverTest;

@RunWith(Suite.class)
@SuiteClasses({ CompletionSuite.class, PreferenceSuite.class,
      JMLHoverTest.class })
public class AllUITests {

}
