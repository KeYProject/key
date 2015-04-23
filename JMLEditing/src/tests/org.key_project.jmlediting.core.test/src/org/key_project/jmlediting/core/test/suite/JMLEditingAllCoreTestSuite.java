package org.key_project.jmlediting.core.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.core.test.dom.ASTNodeTest;
import org.key_project.jmlediting.core.test.dom.ASTSearchTest;
import org.key_project.jmlediting.core.test.dom.ASTTraversalTest;
import org.key_project.jmlediting.core.test.parser.LexicalHelperTest;
import org.key_project.jmlediting.core.test.parser.ParserBuilderTest;
import org.key_project.jmlediting.core.test.profile.BasicDerivedProfileTest;
import org.key_project.jmlediting.core.test.profile.JMLPreferencesHelperTest;
import org.key_project.jmlediting.core.test.profile.JMLProfileManagementTest;
import org.key_project.jmlediting.core.test.profile.persistence.DerivedProfilePersistenceTest;
import org.key_project.jmlediting.core.test.profile.syntax.KeywortSortTest;
import org.key_project.jmlediting.core.test.profile.syntax.UserDefinedKeywordTest;

@RunWith(Suite.class)
@SuiteClasses({
   // dom
   ASTNodeTest.class,
   ASTSearchTest.class,
   ASTTraversalTest.class,
   // parser
   LexicalHelperTest.class, 
   ParserBuilderTest.class,
   // profile
   BasicDerivedProfileTest.class,
   JMLPreferencesHelperTest.class,
   JMLProfileManagementTest.class,
   // persistence
   DerivedProfilePersistenceTest.class,
   // syntax
   KeywortSortTest.class,
   UserDefinedKeywordTest.class
})
public class JMLEditingAllCoreTestSuite {
}
