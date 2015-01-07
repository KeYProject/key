package org.key_project.jmlediting.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmledeting.ui.test.hover.JMLHoverTest;
import org.key_project.jmlediting.ui.test.marker.ParseErrorMarkerTest;

@RunWith(Suite.class)
@SuiteClasses({ CompletionSuite.class, PreferenceSuite.class,
      JMLHoverTest.class, KeywordHighlightingSuite.class,
      JMLCommentHighlightingSuite.class, ParseErrorMarkerTest.class })
public class AllUITests {

}
