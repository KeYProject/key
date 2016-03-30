package de.uka.ilkd.key.nui.tests;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import de.uka.ilkd.key.nui.tests.guitests.NUITestSuite;
import de.uka.ilkd.key.nui.tests.junittests.JUnitTestSuite;

@RunWith(Suite.class)
@SuiteClasses({ NUITestSuite.class, JUnitTestSuite.class })

public class AllTests {

}
