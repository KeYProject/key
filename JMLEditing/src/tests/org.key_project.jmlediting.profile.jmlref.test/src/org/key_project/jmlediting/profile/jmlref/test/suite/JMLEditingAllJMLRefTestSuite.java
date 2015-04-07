package org.key_project.jmlediting.profile.jmlref.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.jmlref.test.parser.BehaviorParserTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.ExpressionParserTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.InvariantForTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.MeasuredByTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.ParserRecoveryTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.QuantifierParserTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.RequiresParserTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.SignalsOnlyTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.SignalsTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.SpecificationStatementParserTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.SpecificationStatementTest;
import org.key_project.jmlediting.profile.jmlref.test.parser.StoreRefParserTest;
import org.key_project.jmlediting.profile.jmlref.test.profile.JMLRefDerivedProfileTest;

@RunWith(Suite.class)
@SuiteClasses({
   // parser
   BehaviorParserTest.class,
   ExpressionParserTest.class,
   InvariantForTest.class,
   MeasuredByTest.class,
   ParserRecoveryTest.class,
   QuantifierParserTest.class,
   RequiresParserTest.class,
   SignalsOnlyTest.class,
   SignalsTest.class,
   SpecificationStatementParserTest.class,
   SpecificationStatementTest.class,
   StoreRefParserTest.class,
   // profile
   JMLRefDerivedProfileTest.class
})
public class JMLEditingAllJMLRefTestSuite {

}
