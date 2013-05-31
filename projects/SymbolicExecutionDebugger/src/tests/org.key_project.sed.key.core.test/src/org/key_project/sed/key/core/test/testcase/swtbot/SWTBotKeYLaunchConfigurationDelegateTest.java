/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.test.testcase.swtbot;

import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.launch.KeYLaunchConfigurationDelegate;
import org.key_project.sed.key.core.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * SWTBot tests for {@link KeYLaunchConfigurationDelegate}.
 * @author Martin Hentschel
 */
public class SWTBotKeYLaunchConfigurationDelegateTest extends AbstractKeYDebugTargetTestCase {
   /**
    * Launches a method from the outline.
    */
   public void testLaunchFromOutlineView() throws Exception {
      // Get current settings to restore them in finally block
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      // Increase timeout
      SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 4;
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotKeYLaunchConfigurationDelegateTest_testLaunchFromOutlineView");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/methodPartPOTest/test", project.getProject().getFolder("src"));
      // Store initial environment
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      SWTBotEditor editor = null;
      SWTBotTree debugTree = null;
      try {
         // Open editor
         IEditorPart part = TestUtilsUtil.openEditor(project.getProject().getFile(new Path("src/MethodPartPOTest.java")));
         editor = bot.editorById(part.getSite().getId());
         // Select method in outline
         SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
         TestUtilsUtil.selectInTree(outlineView.bot().tree(), "MethodPartPOTest", "doSomething(int, String, boolean) : int");
         // Start launch
         outlineView.bot().tree().contextMenu("Debug As").menu("&1 Symbolic Execution Debugger (SED)").click();
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         assertNotNull(launch);
         // Resume
         SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
         resume(bot, item, target);
         // Make sure that correct tree is created
         assertDebugTargetViaOracle(target, "data/methodPartPOTest/oracle/MethodPartPOTest_methodName.xml", false, false);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Close opened editor.
         if (editor != null) {
            editor.close();
         }
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         // Restore perspective
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }
   
   /**
    * Launches a method from a text editor where a single statement selected.
    */
   @Test
   public void testLaunchInTextEditorSingleStatementSelected() throws Exception {
      doLaunchInTextEdtiorTest("SWTBotKeYLaunchConfigurationDelegateTest_testLaunchInTextEditorSingleStatementSelected", 
                               Activator.PLUGIN_ID, 
                               "data/methodPartPOTest/test", 
                               "src/MethodPartPOTest.java",
                               27,
                               2,
                               29,
                               "int y = 2 + CONSTANT + field;",
                               "data/methodPartPOTest/oracle/MethodPartPOTest_singleStatement.xml");
   }
   
   /**
    * Launches a method from a text editor where the content of the else block is selected.
    */
   @Test
   public void testLaunchInTextEditorElseBlockSelected() throws Exception {
      doLaunchInTextEdtiorTest("SWTBotKeYLaunchConfigurationDelegateTest_testLaunchInTextEditorElseBlockSelected", 
                               Activator.PLUGIN_ID, 
                               "data/methodPartPOTest/test", 
                               "src/MethodPartPOTest.java",
                               23,
                               3,
                               22,
                               "x -= 42; return x;",
                               "data/methodPartPOTest/oracle/MethodPartPOTest_elseBlock.xml");
   }
   
   /**
    * Launches a method from a text editor where the content of the if block is selected.
    */
   @Test
   public void testLaunchInTextEditorIfBlockSelected() throws Exception {
      doLaunchInTextEdtiorTest("SWTBotKeYLaunchConfigurationDelegateTest_testLaunchInTextEditorIfBlockSelected", 
                               Activator.PLUGIN_ID, 
                               "data/methodPartPOTest/test", 
                               "src/MethodPartPOTest.java",
                               19,
                               3,
                               23,
                               "x = x * -1; x += 2;",
                               "data/methodPartPOTest/oracle/MethodPartPOTest_ifBlock.xml");
   }
   
   /**
    * Launches a method from a text editor where the method name is selected.
    */
   @Test
   public void testLaunchInTextEditorMethodNameSelected() throws Exception {
      doLaunchInTextEdtiorTest("SWTBotKeYLaunchConfigurationDelegateTest_testLaunchInTextEditorMethodNameSelected", 
                               Activator.PLUGIN_ID, 
                               "data/methodPartPOTest/test", 
                               "src/MethodPartPOTest.java",
                               15,
                               15,
                               11,
                               "doSomething",
                               "data/methodPartPOTest/oracle/MethodPartPOTest_methodName.xml");
   }
   
   /**
    * Executes the test steps to launch something from a text editor.
    * @param projectName The project name to use.
    * @param plugin The plug-in which provides the test data.
    * @param pathInBundle The path in the plug-in with the test data.
    * @param pathInProjectToFileToOpen The file in the workspace to open.
    * @param lineToSelect The line to select.
    * @param columnToSelect The column to select.
    * @param selectionLength The selection length.
    * @param expectedSelectedText The expected selected text.
    * @param expectedModelPathInBundle The path to the result file in the plug-in.
    * @throws Exception Occurred Exception.
    */
   protected void doLaunchInTextEdtiorTest(String projectName,
                                           String plugin,
                                           String pathInBundle,
                                           String pathInProjectToFileToOpen,
                                           int lineToSelect,
                                           int columnToSelect,
                                           int selectionLength,
                                           String expectedSelectedText,
                                           String expectedModelPathInBundle) throws Exception {
      // Get current settings to restore them in finally block
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      // Increase timeout
      SWTBotPreferences.TIMEOUT = SWTBotPreferences.TIMEOUT * 4;
      // Create bot
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
      BundleUtil.extractFromBundleToWorkspace(plugin, pathInBundle, project.getProject().getFolder("src"));
      // Store initial environment
      IPerspectiveDescriptor defaultPerspective = TestUtilsUtil.getActivePerspective();
      SWTBotEditor editor = null;
      SWTBotTree debugTree = null;
      try {
         // Open symbolic debug perspective
         TestSedCoreUtil.openSymbolicDebugPerspective();
         // Open editor
         IEditorPart part = TestUtilsUtil.openEditor(project.getProject().getFile(new Path(pathInProjectToFileToOpen)));
         editor = bot.editorById(part.getSite().getId());
         // Select text
         SWTBotStyledText text = editor.bot().styledText(); 
         text.selectRange(lineToSelect, columnToSelect, selectionLength);
         assertTrue("Expected \"" + expectedSelectedText + "\" but is \"" + text.getSelection() + "\".", StringUtil.equalIgnoreWhiteSpace(expectedSelectedText, text.getSelection()));
         // Start launch
         text.contextMenu("Debug As").menu("&1 Symbolic Execution Debugger (SED)").click();
         // Find the launched ILaunch in the debug view
         SWTBotView debugView = TestSedCoreUtil.getDebugView(bot);
         debugTree = debugView.bot().tree();
         ISEDDebugTarget target = TestSedCoreUtil.waitUntilDebugTreeHasDebugTarget(bot, debugTree);
         ILaunch launch = target.getLaunch();
         assertNotNull(launch);
         // Resume
         SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
         resume(bot, item, target);
         // Make sure that correct tree is created
         assertDebugTargetViaOracle(target, expectedModelPathInBundle, false, false);
      }
      finally {
         // Restore timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Close opened editor.
         if (editor != null) {
            editor.close();
         }
         // Terminate and remove all launches
         TestSedCoreUtil.terminateAndRemoveAll(debugTree);
         // Restore perspective
         TestUtilsUtil.openPerspective(defaultPerspective);
      }
   }
}