package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.graphiti.mm.algorithms.styles.Style;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.ui.visualization.util.VisualizationPreferences;

/**
 * Tests the used {@link Style}s in symbolic execution trees.
 * @author Martin Hentschel
 */
public class SWTBotSymbolicExecutionTreeStyleTest extends AbstractSymbolicExecutionTreeTest {
   // TODO: Implement tests for annotations
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeFirstBackgroundColor()}.
    */
   @Test
   public void testFirstBackgroundColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeFirstBackgroundColor();
      try {
         IChange change = new IChange() {
            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeFirstBackgroundColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testFirstBackgroundColorChange", 
                      change, 
                      "ChangeFirstBackgroundColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeFirstBackgroundColor(originalColor);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeSecondBackgroundColor()}.
    */
   @Test
   public void testSecondBackgroundColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeSecondBackgroundColor();
      try {
         IChange change = new IChange() {
            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeSecondBackgroundColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testSecondBackgroundColorChange", 
                      change, 
                      "ChangeSecondBackgroundColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeSecondBackgroundColor(originalColor);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#isExecutionTreeNodeDirectionHorizontal()}.
    */
   @Test
   public void testDirectionChange() throws Exception {
      boolean originalValue = VisualizationPreferences.isExecutionTreeNodeDirectionHorizontal();
      try {
         IChange change = new IChange() {
            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeDirectionHorizontal(false);
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testDirectionChange", 
                      change, 
                      "ChangeBackgroundColorDirection");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeDirectionHorizontal(originalValue);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeForegroundColor()}.
    */
   @Test
   public void testForegroundColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeForegroundColor();
      try {
         IChange change = new IChange() {
            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeForegroundColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testForegroundColorChange", 
                      change, 
                      "ChangeForegroundColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeForegroundColor(originalColor);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeTextColor()}.
    */
   @Test
   public void testTextColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeTextColor();
      try {
         IChange change = new IChange() {
            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeTextColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testTextColorChange", 
                      change, 
                      "ChangeTextColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeTextColor(originalColor);
      }
   }
   
   /**
    * Launches "data/Number/test/Number.set" and test a change of
    * {@link VisualizationPreferences#getExecutionTreeNodeConnectionColor()}.
    */
   @Test
   public void testConnectionColorChange() throws Exception {
      RGB originalColor = VisualizationPreferences.getExecutionTreeNodeConnectionColor();
      try {
         IChange change = new IChange() {
            @Override
            public void change(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
               VisualizationPreferences.setExecutionTreeNodeConnectionColor(new RGB(255, 0, 0));
            }
         };
         doChangeTest("SWTBotSymbolicExecutionTreeStyleTest_testConnectionColorChange", 
                      change, 
                      "ChangeConnectionColor");
      }
      finally {
         VisualizationPreferences.setExecutionTreeNodeConnectionColor(originalColor);
      }
   }
   
   /**
    * Launches the example {@code data/Number/test/Number.set},
    * compares it with oracle, performs a change and compares it with oracle again.
    * @param projectName The name of the project to use.
    * @param change The {@link IChange} to perform.
    * @param oracleSuffix The suffix of the second oracle file after the change.
    * @throws Exception Occurred Exception.
    */
   protected void doChangeTest(String projectName,
                               final IChange change,
                               final String oracleSuffix) throws Exception {
      IDiagramTestSteps steps = new IDiagramTestSteps() {
         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            assertDiagram(bot, project, "Number.set", "data/Number/oracle", null);
            change.change(bot, project, setFile, debugView, debugTree, launch, target);
            assertDiagram(bot, project, "Number.set", "data/Number/oracle", oracleSuffix);
         }
      };
      doDiagramTest(projectName, 
                    "data/Number/test", 
                    "Number.set", 
                    steps, 
                    new PathReplacement("D:\\Forschung\\Development\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\Number.java", "Number.java"));
   }
   
   /**
    * Performs a change during {@link SWTBotSymbolicExecutionTreeStyleTest#doChangeTest(IChange, String)}.
    * @author Martin Hentschel
    */
   protected static interface IChange {
      /**
       * Performs the change.
       * @param bot The used {@link SWTWorkbenchBot}.
       * @param project The {@link IProject} which contains the SET file.
       * @param setFile The SET file.
       * @param debugView The debug view.
       * @param debugTree The debug tree.
       * @param launch The {@link ILaunch}.
       * @param target The {@link ISEDDebugTarget}.
       */
      public void change(SWTWorkbenchBot bot, 
                         IProject project, 
                         IFile setFile, 
                         SWTBotView debugView, 
                         SWTBotTree debugTree, 
                         ILaunch launch, 
                         ISEDDebugTarget target) throws Exception;
   }
}
