package org.key_project.jmlediting.core.test;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.core.test.dom.DOMTestSuite;
import org.key_project.jmlediting.core.test.parser.ParserTestSuite;
import org.key_project.jmlediting.core.test.profile.ProfileTestSuite;
import org.key_project.jmlediting.core.test.profile.persistence.DerivedProfilePersistenceTest;
import org.key_project.jmlediting.core.test.profile.syntax.KeywortSortTest;
import org.key_project.jmlediting.core.test.profile.syntax.UserDefinedKeywordTest;
import org.key_project.jmlediting.core.test.utilities.JMLJavaVisibleFieldsComputerTest;
import org.key_project.jmlediting.core.test.utilities.JMLLocatorTest;

@RunWith(Suite.class)
@SuiteClasses({ DOMTestSuite.class, ParserTestSuite.class,
      ProfileTestSuite.class, JMLLocatorTest.class, KeywortSortTest.class,
      DerivedProfilePersistenceTest.class,
      JMLJavaVisibleFieldsComputerTest.class, UserDefinedKeywordTest.class })
public class AllCoreTestsSuite {

}
