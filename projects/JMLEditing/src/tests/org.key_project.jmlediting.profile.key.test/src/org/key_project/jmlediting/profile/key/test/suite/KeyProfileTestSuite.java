package org.key_project.jmlediting.profile.key.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.key.test.locset.KeyAccessibleTest;
import org.key_project.jmlediting.profile.key.test.locset.LocSetExprTest;
import org.key_project.jmlediting.profile.key.test.other.KeyInvariantTest;

@RunWith(Suite.class)
@SuiteClasses({ KeyAccessibleTest.class, LocSetExprTest.class,
      KeyInvariantTest.class })
public class KeyProfileTestSuite {

}
