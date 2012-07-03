package org.key_project.sed.key.core.test.testcase.swtbot;

import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.key4eclipse.starter.core.util.KeYUtil;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.util.KeYSEDPreferences;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Tests the launch configuration default values.
 * @author Martin Hentschel
 */
public class SWTBotLaunchDefaultPreferencesTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Tests the launch where variable values are shown.
    */
   @Test
   public void testShowVariableValues() throws Exception {
      doTestShowVariableValues("SWTBotLaunchDefaultPreferencesTest_testShowVariableValues", true);
   }

   /**
    * Tests the launch where variable values are hidden.
    */
   @Test
   public void testDoNotShowVariableValues() throws Exception {
      doTestShowVariableValues("SWTBotLaunchDefaultPreferencesTest_testDoNotShowVariableValues", false);
   }
   
   /**
    * Does the test steps of {@link #testShowVariableValues()}
    * and {@link #testDoNotShowVariableValues()}.
    * @param projectName The project name to use.
    * @param showVariableValues Show variable values?
    * @throws Exception Occurred Exception
    */
   protected void doTestShowVariableValues(String projectName, 
                                           final boolean showVariableValues) throws Exception {
      boolean originalShowVariableValues = KeYSEDPreferences.isShowVariablesOfSelectedDebugNode();
      try {
         // Set preference
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         SWTBotShell preferenceShell = TestUtilsUtil.openPreferencePage(bot, "Run/Debug", "Symbolic Execution Debugger (SED)", "KeY Launch Defaults");
         if (showVariableValues) {
            preferenceShell.bot().checkBox("Show variables of selected debug node").select();
         }
         else {
            preferenceShell.bot().checkBox("Show variables of selected debug node").deselect();
         }
         preferenceShell.bot().button("OK").click();
         assertEquals(showVariableValues, KeYSEDPreferences.isShowVariablesOfSelectedDebugNode());
         // Launch something
         IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
            @Override
            public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
               // Get debug target TreeItem
               SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
               // Do run
               resume(bot, item, target);
               // Select statement int result;
               item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0, 1); 
               // Wait for jobs
               TestUtilsUtil.waitForJobs();
               // Get variables view
               SWTBotView variablesView = TestSedCoreUtil.getVariablesView(bot);
               SWTBotTree variablesTree = variablesView.bot().tree();
               SWTBotTreeItem[] items = variablesTree.getAllItems();
               assertEquals(items != null ? "items found: " + items.length : "items are null", showVariableValues, !ArrayUtil.isEmpty(items));
            }
         };
         doKeYDebugTargetTest(projectName,
                              "data/simpleIf/test",
                              true,
                              true,
                              createMethodSelector("SimpleIf", "min", "I", "I"),
                              Boolean.FALSE,
                              null,
                              Boolean.FALSE,
                              8,
                              executor);
      }
      finally {
         // Restore original value
         KeYSEDPreferences.setShowVariablesOfSelectedDebugNode(originalShowVariableValues);
         assertEquals(originalShowVariableValues, KeYSEDPreferences.isShowVariablesOfSelectedDebugNode());
      }
   }
   
   /**
    * Tests a launch in which KeY's main window is shown.
    */
   @Test
   public void testShowKeYMainWindow() throws Exception {
      doTestMainWindowLaunch("SWTBotLaunchDefaultPreferencesTest_testShowKeYMainWindow", true);
   }

   /**
    * Tests a launch in which KeY's main window is not shown.
    */
   @Test
   public void testDoNotShowKeYMainWindow() throws Exception {
      doTestMainWindowLaunch("SWTBotLaunchDefaultPreferencesTest_testDoNotShowKeYMainWindow", false);
   }
   
   /**
    * Executes the test steps of {@link #testShowKeYMainWindow()} and
    * {@link #testDoNotShowKeYMainWindow()}.
    * @param projectName The name of the java project to use.
    * @param showMainWindow {@code true} show main window, {@code false} hide main window.
    */
   protected void doTestMainWindowLaunch(String projectName, 
                                         final boolean showMainWindow) throws Exception {
      boolean originalShowMainWindow = KeYSEDPreferences.isShowKeYMainWindow();
      try {
         // Make sure that KeY's main window is hidden and contains no proofs.
         if (MainWindow.hasInstance()) {
            KeYUtil.clearProofList(MainWindow.getInstance(false));
            MainWindow.getInstance(false).setVisible(false);
         }
         // Set preference
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         SWTBotShell preferenceShell = TestUtilsUtil.openPreferencePage(bot, "Run/Debug", "Symbolic Execution Debugger (SED)", "KeY Launch Defaults");
         if (showMainWindow) {
            preferenceShell.bot().checkBox("Show KeY's main window (only for experienced user)").select();
         }
         else {
            preferenceShell.bot().checkBox("Show KeY's main window (only for experienced user)").deselect();
         }
         preferenceShell.bot().button("OK").click();
         assertEquals(showMainWindow, KeYSEDPreferences.isShowKeYMainWindow());
         // Launch something
         IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
            @Override
            public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
               if (showMainWindow) {
                  assertTrue(MainWindow.hasInstance());
                  assertTrue(MainWindow.getInstance(false).isVisible());
                  assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance(false)));
               }
               else {
                  if (MainWindow.hasInstance()) {
                     assertFalse(MainWindow.getInstance(false).isVisible());
                     assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance(false)));
                  }
               }
            }
         };
         doKeYDebugTargetTest(projectName,
                              "data/simpleIf/test",
                              true,
                              true,
                              createMethodSelector("SimpleIf", "min", "I", "I"),
                              Boolean.FALSE,
                              Boolean.FALSE,
                              null,
                              8,
                              executor);
      }
      finally {
         // Restore original value
         KeYSEDPreferences.setShowMethodReturnValuesInDebugNode(originalShowMainWindow);
         assertEquals(originalShowMainWindow, KeYSEDPreferences.isShowMethodReturnValuesInDebugNode());
      }
   }
   
   /**
    * Tests the launch where return values are shown in tree.
    */
   @Test
   public void testShowMethodReturnValuesInDebugNodes() throws Exception {
      doTestShowMethodReturnValuesInDebugNodes("SWTBotLaunchDefaultPreferencesTest_testShowMethodReturnValuesInDebugNodes", true);
   }

   /**
    * Tests the launch where return values are not shown in tree.
    */
   @Test
   public void testDoNotShowMethodReturnValuesInDebugNodes() throws Exception {
      doTestShowMethodReturnValuesInDebugNodes("SWTBotLaunchDefaultPreferencesTest_testDoNotShowMethodReturnValuesInDebugNodes", false);
   }
   
   /**
    * Does the test steps of {@link #testShowMethodReturnValuesInDebugNodes()}
    * and {@link #testDoNotShowMethodReturnValuesInDebugNodes()}.
    * @param projectName The project name to use.
    * @param showMethodReturnValuesInDebugNodes Show method return values in debug node?
    * @throws Exception Occurred Exception
    */
   protected void doTestShowMethodReturnValuesInDebugNodes(String projectName, 
                                                           final boolean showMethodReturnValuesInDebugNodes) throws Exception {
      boolean originalShowMethodReturnValuesInDebugNodes = KeYSEDPreferences.isShowMethodReturnValuesInDebugNode();
      try {
         // Set preference
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         SWTBotShell preferenceShell = TestUtilsUtil.openPreferencePage(bot, "Run/Debug", "Symbolic Execution Debugger (SED)", "KeY Launch Defaults");
         if (showMethodReturnValuesInDebugNodes) {
            preferenceShell.bot().checkBox("Show method return values in debug nodes").select();
         }
         else {
            preferenceShell.bot().checkBox("Show method return values in debug nodes").deselect();
         }
         preferenceShell.bot().button("OK").click();
         assertEquals(showMethodReturnValuesInDebugNodes, KeYSEDPreferences.isShowMethodReturnValuesInDebugNode());
         // Launch something
         IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
            @Override
            public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
               // Get debug target TreeItem
               SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
               // Do resume and test created tree
               String expectedModelPathInBundle = showMethodReturnValuesInDebugNodes ? "data/simpleIf/oracle/SimpleIf.xml" : "data/simpleIf/oracle_noMethodReturnValues/SimpleIf.xml";
               resume(bot, item, target);
               assertDebugTargetViaOracle(target, expectedModelPathInBundle, false, false);
            }
         };
         doKeYDebugTargetTest(projectName,
                              "data/simpleIf/test",
                              true,
                              true,
                              createMethodSelector("SimpleIf", "min", "I", "I"),
                              null,
                              Boolean.FALSE,
                              Boolean.FALSE,
                              8,
                              executor);
      }
      finally {
         // Restore original value
         KeYSEDPreferences.setShowMethodReturnValuesInDebugNode(originalShowMethodReturnValuesInDebugNodes);
         assertEquals(originalShowMethodReturnValuesInDebugNodes, KeYSEDPreferences.isShowMethodReturnValuesInDebugNode());
      }
   }
}
