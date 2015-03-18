package org.key_project.jmlediting.profile.key.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.key.test.locset.KeyAccessibleTest;
import org.key_project.jmlediting.profile.key.test.locset.LocSetExprTest;
import org.key_project.jmlediting.profile.key.test.other.DynamicLogicPrimaryTest;
import org.key_project.jmlediting.profile.key.test.other.IndexTest;
import org.key_project.jmlediting.profile.key.test.other.KeyInvariantTest;
import org.key_project.jmlediting.profile.key.test.seq.SeqExprTest;
import org.key_project.jmlediting.profile.key.test.spec_statement.SpecStatementsTest;

@RunWith(Suite.class)
@SuiteClasses({ KeyAccessibleTest.class, LocSetExprTest.class,
      KeyInvariantTest.class, SeqExprTest.class, IndexTest.class,
      SeqExprTest.class, DynamicLogicPrimaryTest.class,
      SpecStatementsTest.class })
public class KeyProfileTestSuite {

}
