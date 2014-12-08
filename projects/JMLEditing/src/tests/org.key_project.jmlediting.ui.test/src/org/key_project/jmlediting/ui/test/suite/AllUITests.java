package org.key_project.jmlediting.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmledeting.ui.test.hover.JMLHoverTest;
import org.key_project.jmlediting.ui.test.highlighting.JMLLocatorTest;

@RunWith(Suite.class)
@SuiteClasses({ CompletionSuite.class, JMLLocatorTest.class,
   PreferenceSuite.class, JMLHoverTest.class })
public class AllUITests {

}
