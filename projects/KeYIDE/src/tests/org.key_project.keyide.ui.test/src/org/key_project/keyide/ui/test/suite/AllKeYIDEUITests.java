package org.key_project.keyide.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.keyide.ui.test.testcase.*;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   TreeViewerIteratorTest.class,
   OutlineContentAndLabelProviderTest.class
})
public class AllKeYIDEUITests {
}
