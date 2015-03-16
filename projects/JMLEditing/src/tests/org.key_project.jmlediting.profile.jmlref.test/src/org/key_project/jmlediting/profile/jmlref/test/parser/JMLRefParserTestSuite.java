package org.key_project.jmlediting.profile.jmlref.test.parser;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({ SpecificationStatementParserTest.class,
      BehaviorParserTest.class, ExpressionParserTest.class,
      QuantifierParserTest.class, RequiresParserTest.class,
      InvariantForTest.class, MeasuredByTest.class, SignalsTest.class,
      SignalsOnlyTest.class, ParserRecoveryTest.class })
public class JMLRefParserTestSuite {

}
