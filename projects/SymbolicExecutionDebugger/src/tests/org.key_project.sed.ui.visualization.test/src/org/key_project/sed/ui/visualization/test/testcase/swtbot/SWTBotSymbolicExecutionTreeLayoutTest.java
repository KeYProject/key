package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.visualization.execution_tree.feature.AbstractDebugNodeUpdateFeature;
import org.key_project.sed.ui.visualization.execution_tree.feature.DebugTargetConnectFeature;
import org.key_project.sed.ui.visualization.test.util.TestVisualizationUtil;

/**
 * Tests the automatic layout of symbolic execution trees via
 * {@link DebugTargetConnectFeature} and {@link AbstractDebugNodeUpdateFeature}.
 * @author Martin Hentschel
 */
public class SWTBotSymbolicExecutionTreeLayoutTest extends AbstractSymbolicExecutionTreeTest {
   /**
    * Launches "data/Number/test/Number.set" and tests shown diagram.
    */
//   @Test
//   public void testNumber() throws Exception {
//      doLayoutTest("SWTBotSymbolicExecutionTreeLayoutTest_testNumber", 
//                   "data/Number/test", 
//                   "Number.set",
//                   "data/Number/oracle",
//                   new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example1\\Number.java", "Number.java"));
////                   new PathReplacement("D:\\Forschung\\Development\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example1\\Number.java", "Number.java"));
//   }
   
   /**
    * Launches "data/ThesisExample/test/ThesisExample.set" and tests shown diagram.
    */
   @Test
   public void testThesisExample() throws Exception {
      doLayoutTest("SWTBotSymbolicExecutionTreeLayoutTest_testThesisExample", 
                   "data/ThesisExample/test",
                   "ThesisExample.set",
                   "data/ThesisExample/oracle",
                   new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example5\\ThesisExample.java", "ThesisExample.java"));
   }
   
   /**
    * Launches "TODO" and tests the collapse function on the most outer group
    */
   @Test
   public void testCollapseOuterGroup() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the expand function on the most outer group
    */
   @Test
   public void testExpandOuterGroup() throws Exception {
      
   }

   /**
    * Launches "TODO" and tests the collapse function on a group with
    * no previous branch
    */
   @Test
   public void testCollapseGroupNoPrev() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the expand function on a group with
    * no previous branch
    */
   @Test
   public void testExpandGroupNoPrev() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the collapse function on a group with
    * a previous branch
    */
   @Test
   public void testCollapseGroupWithPrev() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the expand function on a group with
    * a previous branch
    */
   @Test
   public void testExpandGroupWithPrev() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the collapse function on a loop
    */
   @Test
   public void testCollapseLoop() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the expand function on a loop
    */
   @Test
   public void testExpandLoop() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the collapse function on the iterations
    * of a loop
    */
   @Test
   public void testCollapseLoopIterations() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the expand function on the iterations
    * of a loop
    */
   @Test
   public void testExpandLoopIterations() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the automatic collapse of the diagram
    */
   @Test
   public void testAutoCollapseResume() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the automatic collapse of groups
    * with StepInto-Execution
    */   
   @Test
   public void testAutoCollapseStepInto() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the left special case specified in
    * "Guided Navigations in Symbolic Execution Trees" chapter 5.2.2
    */
   @Test
   public void testBigNodeSmallSubtreeLeft() throws Exception {
      
   }
   
   /**
    * Launches "TODO" and tests the right special case specified in
    * "Guided Navigations in Symbolic Execution Trees" chapter 5.2.2
    */   
   @Test
   public void testBigNodeSmallSubtreeRight() throws Exception {
      
   }
   
//   @Test
//   public void testCollapse() throws Exception {
//      IDiagramTestSteps steps = new AbstractDiagramTestSteps() {
//
//         @Override
//         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
//            assertDiagram(bot, project, "Number2.set", "data/Number2/oracle", null);
//            SWTBotGefEditor editor = TestVisualizationUtil.getSymbolicExecutionTreeViewGefEditor(bot);
//            editor.select("<call self.equals(n)>");
//            editor.clickContextMenu("Collapse");
//            assertDiagram(bot, project, "Number2.set", "data/Number2/oracle", "Collapsed");
//         }
//
//      };
//      
//      doDiagramTest("SWTBotSymbolicExecutionTreeLayoutTest_testNumber2", 
//            "data/Number2/test",
//            "Number2.set",
//            steps,
//            new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example5\\Number2.java", "Number2.java"));
//   }
}
