package org.key_project.jmlediting.profile.key.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.key.test.bounded_quantifier.BSumProdTest;
import org.key_project.jmlediting.profile.key.test.locset.KeYAccessibleTest;
import org.key_project.jmlediting.profile.key.test.locset.LocSetExprTest;
import org.key_project.jmlediting.profile.key.test.other.DynamicLogicPrimaryTest;
import org.key_project.jmlediting.profile.key.test.other.ElemsTest;
import org.key_project.jmlediting.profile.key.test.other.KeYBehaviorTest;
import org.key_project.jmlediting.profile.key.test.other.KeYInvariantTest;
import org.key_project.jmlediting.profile.key.test.other.OverridenKeywordTest;
import org.key_project.jmlediting.profile.key.test.seq.IndexTest;
import org.key_project.jmlediting.profile.key.test.seq.SeqExprTest;
import org.key_project.jmlediting.profile.key.test.seq.SeqTest;
import org.key_project.jmlediting.profile.key.test.spec_statement.SpecStatementsTest;

@RunWith(Suite.class)
@SuiteClasses({ 
   // bounded quantifier
   BSumProdTest.class,
   // locset
   KeYAccessibleTest.class,
   LocSetExprTest.class,
   // other
   DynamicLogicPrimaryTest.class,
   ElemsTest.class,
   KeYBehaviorTest.class,
   KeYInvariantTest.class,
   OverridenKeywordTest.class,
   // seq
   IndexTest.class,
   SeqExprTest.class,
   SeqTest.class,
   // spec_statement
   SpecStatementsTest.class
})
public class JMLEditingAllKeYProfileTestSuite {

}
