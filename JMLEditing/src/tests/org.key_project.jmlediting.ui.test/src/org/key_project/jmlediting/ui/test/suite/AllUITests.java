package org.key_project.jmlediting.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.core.test.AllCoreTestsSuite;
import org.key_project.jmlediting.profile.jmlref.test.suite.JMLRefTestSuite;
import org.key_project.jmlediting.profile.key.test.suite.KeyProfileTestSuite;
import org.key_project.jmlediting.ui.test.formatter.FormatterTest;
import org.key_project.jmlediting.ui.test.formatter.MultilineCommentEditingTest;
import org.key_project.jmlediting.ui.test.hover.JMLHoverTest;
import org.key_project.jmlediting.ui.test.marker.ParseErrorMarkerTest;
import org.key_project.jmlediting.ui.test.marker.ValidationErrorMarkerTest;

@RunWith(Suite.class)
@SuiteClasses({ AllCoreTestsSuite.class, JMLRefTestSuite.class,
      KeyProfileTestSuite.class, PreferenceSuite.class, JMLHoverTest.class,
      HighlightingSuite.class, ParseErrorMarkerTest.class,
      ValidationErrorMarkerTest.class, MultilineCommentEditingTest.class,
      CompletionSuite.class, FormatterTest.class })
public class AllUITests {

}
