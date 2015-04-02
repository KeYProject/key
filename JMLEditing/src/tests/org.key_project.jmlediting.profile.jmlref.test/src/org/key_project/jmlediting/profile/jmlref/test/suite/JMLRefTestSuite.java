package org.key_project.jmlediting.profile.jmlref.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.jmlref.test.parser.JMLRefParserTestSuite;
import org.key_project.jmlediting.profile.jmlref.test.profile.JMLRefDerivedProfileTest;

@RunWith(Suite.class)
@SuiteClasses({ JMLRefParserTestSuite.class, JMLRefDerivedProfileTest.class })
public class JMLRefTestSuite {

}
