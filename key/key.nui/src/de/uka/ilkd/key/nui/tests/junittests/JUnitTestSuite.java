package de.uka.ilkd.key.nui.tests.junittests;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;
/**
 * Test suite for application logic tests based on JUnit.
 * 
 * @author Patrick Jattke
 *
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({ SearchTest.class, StyleConfigurationTest.class, ExpandCollapseTest.class,
        FreeTextFilterTest.class, PredefFilterTest.class, TreeViewControllerTest.class })

@SuppressWarnings("PMD.AtLeastOneConstructor")
// PMD will also complain if adding the constructor, then saying "avoid useless
// constructors"
public class JUnitTestSuite {

}
