package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
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
                   new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example1\\Number.java", "Number.java"));
//                   new PathReplacement("D:\\Forschung\\Development\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example1\\Number.java", "Number.java"));
   }
   
   /**
    * Launches "data/Number2/test/Number2.set" and tests shown diagram.
    */
   @Test
   public void testNumber2() throws Exception {
      doLayoutTest("SWTBotSymbolicExecutionTreeLayoutTest_testNumber2", 
                   "data/Number2/test",
                   "Number2.set",
                   "data/Number2/oracle",
                   new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example5\\Number2.java", "Number2.java"));
   }
   
   @Test
   public void testCollapse() throws Exception {
      IDiagramTestSteps steps = new AbstractDiagramTestSteps() {

         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            assertDiagram(bot, project, "Number2.set", "data/Number2/oracle", null);

            assertDiagram(bot, project, "Number2.set", "data/Number2/oracle", "Collapsed");
         }

      };
      
      doDiagramTest("SWTBotSymbolicExecutionTreeLayoutTest_testNumber2", 
            "data/Number2/test",
            "Number2.set",
            steps,
            new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example5\\Number2.java", "Number2.java"));
   }
}
