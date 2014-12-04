package org.key_project.jmlediting.core.test;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.core.test.dom.DOMTestSuite;
import org.key_project.jmlediting.core.test.parser.ParserTestSuite;
import org.key_project.jmlediting.core.test.profile.ProfileTestSuite;

@RunWith(Suite.class)
@SuiteClasses({ DOMTestSuite.class, ParserTestSuite.class,
      ProfileTestSuite.class })
public class AllCoreTestsSuite {

}
