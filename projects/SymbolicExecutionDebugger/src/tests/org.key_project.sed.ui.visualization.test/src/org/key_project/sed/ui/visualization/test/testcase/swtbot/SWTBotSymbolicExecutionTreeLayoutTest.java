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
    * Launches "data/ThesisExample/test/ThesisExample.set" and tests the shown diagram.
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
    * Launches "data/ThesisExample/test/ThesisExample.set" and tests the collapse and the expand function on the most outer group
    */
   @Test
   public void testCollapseExpandOuterGroup() throws Exception {
      IDiagramTestSteps steps = new AbstractDiagramTestSteps() {

         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            assertDiagram(bot, project, "ThesisExample.set", "data/ThesisExample/oracle", null);
            SWTBotGefEditor editor = TestVisualizationUtil.getSymbolicExecutionTreeViewGefEditor(bot);
            editor.select("<call self.magic(other)>");
            editor.clickContextMenu("Collapse");
            assertDiagram(bot, project, "ThesisExampleCollapsedOuterGroup.set", "data/ThesisExample/oracle", null);
            editor.select("<call self.magic(other)>");
            editor.clickContextMenu("Expand");
            assertDiagram(bot, project, "ThesisExampleExpandedOuterGroup.set", "data/ThesisExample/oracle", null);
         }

      };
      
      doDiagramTest("SWTBotSymbolicExecutionTreeLayoutTest_testCollapseExpandOuterGroup", 
            "data/ThesisExample/test",
            "ThesisExample.set",
            steps,
            new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example5\\ThesisExample.java", "ThesisExample.java"));
   }
   
   /**
    * Launches "data/ThesisExample/test/ThesisExample.set" and tests the collapse and the expand function on a group with
    * no previous branch
    */
   @Test
   public void testCollapseExpandGroupNoPrev() throws Exception {
      IDiagramTestSteps steps = new AbstractDiagramTestSteps() {

         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            assertDiagram(bot, project, "ThesisExample.set", "data/ThesisExample/oracle", null);
            SWTBotGefEditor editor = TestVisualizationUtil.getSymbolicExecutionTreeViewGefEditor(bot);
            editor.select("if (this.intValue==other.intValue)");
            editor.clickContextMenu("Collapse");
            assertDiagram(bot, project, "ThesisExampleCollapsedGroupNoPrev.set", "data/ThesisExample/oracle", null);
            editor.select("if (this.intValue==other.intValue)");
            editor.clickContextMenu("Expand");
            assertDiagram(bot, project, "ThesisExampleExpandedGroupNoPrev.set", "data/ThesisExample/oracle", null);
         }

      };
      
      doDiagramTest("SWTBotSymbolicExecutionTreeLayoutTest_testCollapseExpandGroupNoPrev", 
            "data/ThesisExample/test",
            "ThesisExample.set",
            steps,
            new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example5\\ThesisExample.java", "ThesisExample.java"));
   }

   /**
    * Launches "data/ThesisExample/test/ThesisExample.set" and tests the collapse and the expand function on a group with
    * a previous branch
    */
   @Test
   public void testCollapseExpandGroupWithPrev() throws Exception {
      IDiagramTestSteps steps = new AbstractDiagramTestSteps() {

         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            assertDiagram(bot, project, "ThesisExample.set", "data/ThesisExample/oracle", null);
            SWTBotGefEditor editor = TestVisualizationUtil.getSymbolicExecutionTreeViewGefEditor(bot);
            editor.select("for ( int i = 0; i<2; i++ )");
            editor.clickContextMenu("Collapse");
            assertDiagram(bot, project, "ThesisExampleCollapsedGroupWithPrev.set", "data/ThesisExample/oracle", null);
            editor.select("for ( int i = 0; i<2; i++ )");
            editor.clickContextMenu("Expand");
            assertDiagram(bot, project, "ThesisExampleExpandedGroupWithPrev.set", "data/ThesisExample/oracle", null);
         }

      };
      
      doDiagramTest("SWTBotSymbolicExecutionTreeLayoutTest_testCollapseExpandGroupWithPrev", 
            "data/ThesisExample/test",
            "ThesisExample.set",
            steps,
            new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example5\\ThesisExample.java", "ThesisExample.java"));
   }
   
   /**
    * Launches "data/ThesisExample/test/ThesisExample.set" and tests the collapse and the expand function on the iterations
    * of a loop
    */
   @Test
   public void testCollapseExpandLoopIterations() throws Exception {
      IDiagramTestSteps steps = new AbstractDiagramTestSteps() {

         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            assertDiagram(bot, project, "ThesisExample.set", "data/ThesisExample/oracle", null);
            SWTBotGefEditor editor = TestVisualizationUtil.getSymbolicExecutionTreeViewGefEditor(bot);
            editor.select("i<2");
            editor.clickContextMenu("Collapse");
            assertDiagram(bot, project, "ThesisExampleCollapsedLoopIterations.set", "data/ThesisExample/oracle", null);
            editor.select("i<2");
            editor.clickContextMenu("Expand");
            assertDiagram(bot, project, "ThesisExampleExpandedLoopIterations.set", "data/ThesisExample/oracle", null);
         }

      };
      
      doDiagramTest("SWTBotSymbolicExecutionTreeLayoutTest_testCollapseExpandGroupWithPrev", 
            "data/ThesisExample/test",
            "ThesisExample.set",
            steps,
            new PathReplacement("D:\\BA\\git\\key\\projects\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\example5\\ThesisExample.java", "ThesisExample.java"));
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
}
