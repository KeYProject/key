package org.key_project.jmlediting.profile.key.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.key.test.bounded_quantifier.BSumProdTest;
import org.key_project.jmlediting.profile.key.test.locset.KeyAccessibleTest;
import org.key_project.jmlediting.profile.key.test.locset.LocSetExprTest;
import org.key_project.jmlediting.profile.key.test.other.DynamicLogicPrimaryTest;
import org.key_project.jmlediting.profile.key.test.other.ElemsTest;
import org.key_project.jmlediting.profile.key.test.other.KeyInvariantTest;
import org.key_project.jmlediting.profile.key.test.seq.IndexTest;
import org.key_project.jmlediting.profile.key.test.seq.SeqExprTest;
import org.key_project.jmlediting.profile.key.test.spec_statement.SpecStatementsTest;

@RunWith(Suite.class)
@SuiteClasses({ KeyAccessibleTest.class, LocSetExprTest.class,
      KeyInvariantTest.class, SeqExprTest.class, IndexTest.class,
      SeqExprTest.class, DynamicLogicPrimaryTest.class,
      SpecStatementsTest.class, BSumProdTest.class, ElemsTest.class })
public class KeyProfileTestSuite {

}
