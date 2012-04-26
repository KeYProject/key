package org.key_project.sed.ui.visualization.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.ui.visualization.test.testcase.AbstractDebugViewBasedEditorInViewViewTest;
import org.key_project.sed.ui.visualization.test.testcase.EditableMultiDeleteInfoTest;
import org.key_project.sed.ui.visualization.test.testcase.ExecutionTreeUtilTest;
import org.key_project.sed.ui.visualization.test.testcase.GraphitiUtilTest;
import org.key_project.sed.ui.visualization.test.testcase.LogUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   AbstractDebugViewBasedEditorInViewViewTest.class,
   EditableMultiDeleteInfoTest.class,
   ExecutionTreeUtilTest.class,
   GraphitiUtilTest.class,
   LogUtilTest.class
})
public class AllSEDUIVisualizationTests {
}
