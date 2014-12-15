package org.key_project.jmlediting.core.test.parser;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({ SpecificationStatementParserTest.class,
      BehaviorParserTest.class, LexicalHelperTest.class,
   StoreRefParserTest.class, ParserBuilderTest.class })
public class ParserTestSuite {

}
