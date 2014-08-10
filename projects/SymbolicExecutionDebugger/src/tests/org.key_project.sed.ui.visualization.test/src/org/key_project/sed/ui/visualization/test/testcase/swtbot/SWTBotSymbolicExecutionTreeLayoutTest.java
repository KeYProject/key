package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import org.junit.Test;
import org.key_project.sed.ui.visualization.execution_tree.feature.AbstractDebugNodeUpdateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugTargetConnectFeature;

/**
 * Tests the automatic layout of symbolic execution trees via
 * {@link DebugTargetConnectFeature} and {@link AbstractDebugNodeUpdateFeature}.
 * @author Martin Hentschel
 */
public class SWTBotSymbolicExecutionTreeLayoutTest extends AbstractSymbolicExecutionTreeTest {
   /**
    * Launches "data/Number/test/Number.set" and tests shown diagram.
    */
   @Test
   public void testNumber() throws Exception {
      doLayoutTest("SWTBotSymbolicExecutionTreeLayoutTest_testNumber", 
                   "data/Number/test", 
                   "Number.set",
                   "data/Number/oracle",
                   new PathReplacement("D:\\Forschung\\Development\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\Number.java", "Number.java"));
   }
}
