package org.key_project.jmlediting.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.jmlediting.ui.test.highlighting.AllKeywordsHighlightingTest;
import org.key_project.jmlediting.ui.test.highlighting.JMLCommentHighlightingTest;
import org.key_project.jmlediting.ui.test.highlighting.KeywordHighlightingTest;

@RunWith(Suite.class)
@Suite.SuiteClasses({ KeywordHighlightingTest.class,
      AllKeywordsHighlightingTest.class , JMLCommentHighlightingTest.class })
public class HighlightingSuite {

}
