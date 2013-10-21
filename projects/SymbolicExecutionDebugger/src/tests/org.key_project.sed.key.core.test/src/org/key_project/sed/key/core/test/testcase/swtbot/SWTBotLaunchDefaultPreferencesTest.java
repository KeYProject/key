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
    * Tests the launch where branch conditions are merged.
    */
   @Test
   public void testMergeBranchCondtions() throws Exception {
      doTestShowVariableValues("SWTBotLaunchDefaultPreferencesTest_testMergeBranchCondtions", true);
   }

   /**
    * Tests the launch where branch conditions are not merged.
    */
   @Test
   public void testDoNotMergeBranchCondtions() throws Exception {
      doTestShowVariableValues("SWTBotLaunchDefaultPreferencesTest_testDoNotMergeBranchCondtions", false);
   }
   
   /**
    * Does the test steps of {@link #testMergeBranchCondtions()}
    * and {@link #testDoNotMergeBranchCondtions()}.
    * @param projectName The project name to use.
    * @param mergeBranchConditions Merge branch conditions?
    * @throws Exception Occurred Exception
    */
   protected void doTestMergeBranchConditions(String projectName, 
                                              final boolean mergeBranchConditions) throws Exception {
      boolean originalMergeBranchConditions = KeYSEDPreferences.isMergeBranchConditions();
      try {
         // Set preference
         SWTWorkbenchBot bot = new SWTWorkbenchBot();
         SWTBotShell preferenceShell = TestUtilsUtil.openPreferencePage(bot, "Run/Debug", "Symbolic Execution Debugger (SED)", "KeY Launch Defaults");
         if (mergeBranchConditions) {
            preferenceShell.bot().checkBox("Merge branch conditions").select();
         }
         else {
            preferenceShell.bot().checkBox("Merge branch conditions").deselect();
         }
         preferenceShell.bot().button("OK").click();
         assertEquals(mergeBranchConditions, KeYSEDPreferences.isMergeBranchConditions());
         // Launch something
         IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {
            @Override
            public void test(SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, ISEDDebugTarget target, ILaunch launch) throws Exception {
               // Get debug target TreeItem
               SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugTree, 0, 0, 0); // Select thread
               // Do run
               resume(bot, item, target);
               if (mergeBranchConditions) {
                  assertDebugTargetViaOracle(target, "data/switchCaseTest/oracleMergeBranchConditions/SwitchCaseTest.xml", false, false);
               }
               else {
                  assertDebugTargetViaOracle(target, "data/switchCaseTest/oracle/SwitchCaseTest.xml", false, false);
               }
            }
         };
         doKeYDebugTargetTest(projectName,
                              "data/switchCaseTest/test",
                              true,
                              true,
                              createMethodSelector("SwitchCaseTest", "switchCase", "I"),
                              null,
                              null,
                              Boolean.FALSE,
                              Boolean.FALSE,
                              Boolean.FALSE,
                              null,
                              8,
                              executor);
      }
      finally {
         // Restore original value
         KeYSEDPreferences.setMergeBranchConditions(originalMergeBranchConditions);
         assertEquals(originalMergeBranchConditions, KeYSEDPreferences.isMergeBranchConditions());
      }
   }
   
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
                              null,
                              null,
                              Boolean.FALSE,
                              null,
                              Boolean.FALSE,
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
            KeYUtil.clearProofList(MainWindow.getInstance());
            MainWindow.getInstance().setVisible(false);
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
                  assertTrue(MainWindow.getInstance().isVisible());
                  assertFalse(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
               }
               else {
                  if (MainWindow.hasInstance()) {
                     assertFalse(MainWindow.getInstance().isVisible());
                     assertTrue(KeYUtil.isProofListEmpty(MainWindow.getInstance()));
                  }
               }
            }
         };
         doKeYDebugTargetTest(projectName,
                              "data/simpleIf/test",
                              true,
                              true,
                              createMethodSelector("SimpleIf", "min", "I", "I"),
                              null,
                              null,
                              Boolean.FALSE,
                              Boolean.FALSE,
                              null,
                              Boolean.FALSE,
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
                              null,
                              null,
                              Boolean.FALSE,
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