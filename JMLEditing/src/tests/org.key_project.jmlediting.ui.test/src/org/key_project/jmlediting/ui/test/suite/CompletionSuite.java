package org.key_project.jmlediting.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.jmlediting.ui.test.completion.JMLCompletionProposalComputerTest;
import org.key_project.jmlediting.ui.test.completion.StoreRefKeywordProposalsTest;

@RunWith(Suite.class)
@Suite.SuiteClasses({ JMLCompletionProposalComputerTest.class,
      StoreRefKeywordProposalsTest.class })
public class CompletionSuite {

}
