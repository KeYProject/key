package org.key_project.jmlediting.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.ui.test.completion.SWTBotJMLCompletionProposalComputerTest;
import org.key_project.jmlediting.ui.test.completion.SWTBotStoreRefKeywordProposalsTest;
import org.key_project.jmlediting.ui.test.formatter.SWTBotFormatterTest;
import org.key_project.jmlediting.ui.test.formatter.SWTBotMultilineCommentEditingTest;
import org.key_project.jmlediting.ui.test.highlighting.SWTBotAllKeywordsHighlightingTest;
import org.key_project.jmlediting.ui.test.highlighting.SWTBotJMLCommentHighlightingTest;
import org.key_project.jmlediting.ui.test.highlighting.SWTBotKeywordHighlightingTest;
import org.key_project.jmlediting.ui.test.hover.SWTBotJMLHoverTest;
import org.key_project.jmlediting.ui.test.marker.SWTBotParseErrorMarkerTest;
import org.key_project.jmlediting.ui.test.marker.SWTBotValidationErrorMarkerTest;
import org.key_project.jmlediting.ui.test.miscellaneous.SWTBotEnableDisableTest;
import org.key_project.jmlediting.ui.test.preferencepages.SWTBotJMLColorPreferencePageTest;
import org.key_project.jmlediting.ui.test.preferencepages.SWTBotJMLKeywordWizardTest;
import org.key_project.jmlediting.ui.test.preferencepages.SWTBotJMLProfileWizardTest;
import org.key_project.jmlediting.ui.test.preferencepages.SWTBotProfilePropertiesTest;
import org.key_project.jmlediting.ui.test.preferencepages.SWTBotProfilePropertiesTest2;

@RunWith(Suite.class)
@SuiteClasses({ 
   // completion
   SWTBotJMLCompletionProposalComputerTest.class,
   SWTBotStoreRefKeywordProposalsTest.class,
   // formatter
   SWTBotFormatterTest.class,
   SWTBotMultilineCommentEditingTest.class,
   // highlighitng
   SWTBotAllKeywordsHighlightingTest.class,
   SWTBotJMLCommentHighlightingTest.class,
   SWTBotKeywordHighlightingTest.class,
   // hover
   SWTBotJMLHoverTest.class,
   // marker
   SWTBotParseErrorMarkerTest.class,
   SWTBotValidationErrorMarkerTest.class,
   // miscellaneous
   SWTBotEnableDisableTest.class,
   // preferencepages
   SWTBotJMLColorPreferencePageTest.class,
   SWTBotJMLKeywordWizardTest.class,
   SWTBotJMLProfileWizardTest.class,
   SWTBotProfilePropertiesTest.class,
   SWTBotProfilePropertiesTest2.class
})
public class SWTBotJMLEditingAllUITests {

}
