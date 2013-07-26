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

package org.key_project.keyide.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.handlers.StartAutoModeHandler;
import org.key_project.keyide.ui.perspectives.KeYPerspective;
import org.key_project.keyide.ui.starter.KeYIDEMethodStarter;
import org.key_project.keyide.ui.test.Activator;
import org.key_project.keyide.ui.test.testcase.swtbot.SWTBotKeYIDEMethodStarterTest.IStartProofTestRunnable;
import org.key_project.keyide.ui.util.KeYIDEPreferences;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * <p>
 * SWTBot tests for {@link StartAutoModeHandler}.
 * </p>
 * <p>
 * Requires the following JVM settings: -Xms128m -Xmx1024m -XX:MaxPermSize=256m
 * </p>
 * <p>
 * If you got timeout exceptions increase the waiting time with the following
 * additional JVM parameter: -Dorg.eclipse.swtbot.search.timeout=10000
 * </p>
 * @author Niklas Bunzel
 */
public class SWTBotAutoModeHandlerTest extends TestCase {
   /**
    * Tests starting the auto mode. Proof is still open after the auto mode.
    * @throws CoreException
    * @throws ProblemLoaderException 
    */
   @Test
   public void testStartAutoMode_proofOpen() throws CoreException, InterruptedException, ProblemLoaderException {
      String projectName = "SWTBotStartAutoModeHandlerTest_testStartAutoMode_proofOpen";
      IStartProofTestRunnable startProofRunnable = new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "chargeAndRecord(int) : void" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "chargeAndRecord(int) : void");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      };
      // Define starter settings
      String originalStarterId = StarterPreferenceUtil.getSelectedMethodStarterID();
      boolean originalDontAsk = StarterPreferenceUtil.isDontAskForMethodStarter();
      boolean originalDisabled = StarterPreferenceUtil.isMethodStarterDisabled();
      StarterPreferenceUtil.setSelectedMethodStarterID(KeYIDEMethodStarter.STARTER_ID);
      StarterPreferenceUtil.setDontAskForMethodStarter(true);
      StarterPreferenceUtil.setMethodStarterDisabled(false);
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 5;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      final SWTWorkbenchBot bot = new SWTWorkbenchBot();
      try {
         // Close welcome view if available
         TestUtilsUtil.closeWelcomeView(bot);
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
         IFolder src = project.getProject().getFolder("src");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
         // Open PayCard.java
         IEditorPart editorPart = TestUtilsUtil.openEditor(src.getFile("PayCard.java"));
         // Start proof
         startProofRunnable.startProof(projectName, bot, editorPart);
         // Switch to KeY perspective
         SWTBotShell switchShell = bot.shell("Confirm Perspective Switch");
         switchShell.bot().button("Yes").click();
         assertEquals(KeYPerspective.PERSPECTIVE_ID, TestUtilsUtil.getActivePerspective().getId());
         // Select first operation contract and start proof
         SWTBotShell contractShell = bot.shell("Select Contract for Proof in KeY");
         contractShell.bot().table().select(0);
         contractShell.bot().button("OK").click();
         // Make sure that the KeY proof editor is opened and that the proof is not closed
         final SWTBotEditor editor = bot.activeEditor();
         assertEquals(KeYEditor.EDITOR_ID, editor.getReference().getId());
         assertTrue(editor.getReference().getEditor(true) instanceof KeYEditor);
         KeYEditor keyEditor = (KeYEditor)editor.getReference().getEditor(true);
         assertNotNull(keyEditor.getCurrentProof());
         assertFalse(keyEditor.getCurrentProof().closed());
         
         //check that the auto mode is available
         assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is disabled
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         //start auto mode
         TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
         TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getEnvironment().getUi());
         //check that auto mode is not available while auto mode is running
         assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is enabled
         assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         // Make sure that the proof is not closed
         TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getEnvironment().getUi());
         assertFalse(keyEditor.getCurrentProof().closed());
         // Make sure that start is enabled and stop is disabled
         assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled()); 
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
      }
      finally {
         StarterPreferenceUtil.setSelectedMethodStarterID(originalStarterId);
         StarterPreferenceUtil.setDontAskForMethodStarter(originalDontAsk);
         StarterPreferenceUtil.setMethodStarterDisabled(originalDisabled);
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }
   
   /**
    * Tests starting the auto mode. Proof is closed after the auto mode.
    * @throws CoreException
    * @throws ProblemLoaderException 
    */
   @Test
   public void testStartAutoMode_proofClosed() throws CoreException, InterruptedException, ProblemLoaderException {
      String projectName = "SWTBotStartAutoModeHandlerTest_testStartAutoMode";
      IStartProofTestRunnable startProofRunnable = new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "isValid() : void" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "isValid() : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      };
      // Define starter settings
      String originalStarterId = StarterPreferenceUtil.getSelectedMethodStarterID();
      boolean originalDontAsk = StarterPreferenceUtil.isDontAskForMethodStarter();
      boolean originalDisabled = StarterPreferenceUtil.isMethodStarterDisabled();
      StarterPreferenceUtil.setSelectedMethodStarterID(KeYIDEMethodStarter.STARTER_ID);
      StarterPreferenceUtil.setDontAskForMethodStarter(true);
      StarterPreferenceUtil.setMethodStarterDisabled(false);
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 5;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      final SWTWorkbenchBot bot = new SWTWorkbenchBot();
      try {
         // Close welcome view if available
         TestUtilsUtil.closeWelcomeView(bot);
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
         IFolder src = project.getProject().getFolder("src");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
         // Open PayCard.java
         IEditorPart editorPart = TestUtilsUtil.openEditor(src.getFile("PayCard.java"));
         // Start proof
         startProofRunnable.startProof(projectName, bot, editorPart);
         // Switch to KeY perspective
         SWTBotShell switchShell = bot.shell("Confirm Perspective Switch");
         switchShell.bot().button("Yes").click();
         assertEquals(KeYPerspective.PERSPECTIVE_ID, TestUtilsUtil.getActivePerspective().getId());
         // Select first operation contract and start proof
         SWTBotShell contractShell = bot.shell("Select Contract for Proof in KeY");
         contractShell.bot().table().select(0);
         contractShell.bot().button("OK").click();
         // Make sure that the KeY proof editor is opened and that the proof is not closed
         final SWTBotEditor editor = bot.activeEditor();
         assertEquals(KeYEditor.EDITOR_ID, editor.getReference().getId());
         assertTrue(editor.getReference().getEditor(true) instanceof KeYEditor);
         KeYEditor keyEditor = (KeYEditor)editor.getReference().getEditor(true);
         assertNotNull(keyEditor.getCurrentProof());
         assertFalse(keyEditor.getCurrentProof().closed());
         
         //check that the auto mode is available
         assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is disabled
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         //start auto mode
         TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
         TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getEnvironment().getUi());
         //check that auto mode is not available while auto mode is running
         assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is enabled
         assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         // Make sure that the proof is closed
         TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getEnvironment().getUi());
         assertTrue(keyEditor.getCurrentProof().closed());
         // Make sure that start/stop are both disabled
         assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled()); 
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
      }
      finally {
         StarterPreferenceUtil.setSelectedMethodStarterID(originalStarterId);
         StarterPreferenceUtil.setDontAskForMethodStarter(originalDontAsk);
         StarterPreferenceUtil.setMethodStarterDisabled(originalDisabled);
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }
   
   /**
    * Test starts the automode, stops the automode and restarts it till the proof is closed.
    * @throws CoreException
    * @throws InterruptedException
    * @throws ProblemLoaderException
    */
   @Test
   public void testStopAutoMode_RestartAutoMode_ProofClosed() throws CoreException, InterruptedException, ProblemLoaderException{
      String projectName = "SWTBotStopAutoModeHandlerTest_testStopAutoMode_RestartAutoMode_ProofClosed";
      IStartProofTestRunnable startProofRunnable = new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      };
      // Define starter settings
      String originalStarterId = StarterPreferenceUtil.getSelectedMethodStarterID();
      boolean originalDontAsk = StarterPreferenceUtil.isDontAskForMethodStarter();
      boolean originalDisabled = StarterPreferenceUtil.isMethodStarterDisabled();
      StarterPreferenceUtil.setSelectedMethodStarterID(KeYIDEMethodStarter.STARTER_ID);
      StarterPreferenceUtil.setDontAskForMethodStarter(true);
      StarterPreferenceUtil.setMethodStarterDisabled(false);
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 5;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      final SWTWorkbenchBot bot = new SWTWorkbenchBot();
      try {
         // Close welcome view if available
         TestUtilsUtil.closeWelcomeView(bot);
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
         IFolder src = project.getProject().getFolder("src");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
         // Open PayCard.java
         IEditorPart editorPart = TestUtilsUtil.openEditor(src.getFile("PayCard.java"));
         // Start proof
         startProofRunnable.startProof(projectName, bot, editorPart);
         // Switch to KeY perspective
         SWTBotShell switchShell = bot.shell("Confirm Perspective Switch");
         switchShell.bot().button("Yes").click();
         assertEquals(KeYPerspective.PERSPECTIVE_ID, TestUtilsUtil.getActivePerspective().getId());
         // Select first operation contract and start proof
         SWTBotShell contractShell = bot.shell("Select Contract for Proof in KeY");
         contractShell.bot().table().select(0);
         contractShell.bot().button("OK").click();
         // Make sure that the KeY proof editor is opened
         final SWTBotEditor editor = bot.activeEditor();
         assertEquals(KeYEditor.EDITOR_ID, editor.getReference().getId());
         assertTrue(editor.getReference().getEditor(true) instanceof KeYEditor);
         KeYEditor keyEditor = (KeYEditor)editor.getReference().getEditor(true);
         //check that the auto mode is available
         assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is disabled
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         //start auto mode
         TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
         TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getEnvironment().getUi());
         //check that auto mode is not available while auto mode is running
         assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is enabled
         assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
              
         //stop auto mode and wait until it has stopped
         TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Stop Auto Mode"));
         TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getEnvironment().getUi());
         //check that auto mode is available again
         assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is disabled
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         // Make sure that the proof is still open (not closed)
         assertFalse(keyEditor.getCurrentProof().closed());
         //restart auto mode
         TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
         TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getEnvironment().getUi());
         //check that auto mode is not available while auto mode is running
         assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is enabled
         assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getEnvironment().getUi());
         //make sure proof is closed
         assertTrue(keyEditor.getCurrentProof().closed());
         //check that the start and stop buttons are both disabled
         assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
      }
      finally {
         StarterPreferenceUtil.setSelectedMethodStarterID(originalStarterId);
         StarterPreferenceUtil.setDontAskForMethodStarter(originalDontAsk);
         StarterPreferenceUtil.setMethodStarterDisabled(originalDisabled);
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }

   /**
    * Test starts and stops the automode. The proof is still open after automode stopped.
    * @throws CoreException
    * @throws InterruptedException
    * @throws ProblemLoaderException
    */
   @Test
   public void testStopAutoMode_ProofOpen() throws CoreException, InterruptedException, ProblemLoaderException{
      String projectName = "SWTBotStopAutoModeHandlerTest_testStopAutoMode_ProofOpen";
      IStartProofTestRunnable startProofRunnable = new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "chargeAndRecord(int) : void" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "chargeAndRecord(int) : void");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      };
      // Define starter settings
      String originalStarterId = StarterPreferenceUtil.getSelectedMethodStarterID();
      boolean originalDontAsk = StarterPreferenceUtil.isDontAskForMethodStarter();
      boolean originalDisabled = StarterPreferenceUtil.isMethodStarterDisabled();
      StarterPreferenceUtil.setSelectedMethodStarterID(KeYIDEMethodStarter.STARTER_ID);
      StarterPreferenceUtil.setDontAskForMethodStarter(true);
      StarterPreferenceUtil.setMethodStarterDisabled(false);
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 5;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      final SWTWorkbenchBot bot = new SWTWorkbenchBot();
      try {
         // Close welcome view if available
         TestUtilsUtil.closeWelcomeView(bot);
         // Create test project
         IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
         IFolder src = project.getProject().getFolder("src");
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/paycard", src);
         // Open PayCard.java
         IEditorPart editorPart = TestUtilsUtil.openEditor(src.getFile("PayCard.java"));
         // Start proof
         startProofRunnable.startProof(projectName, bot, editorPart);
         // Switch to KeY perspective
         SWTBotShell switchShell = bot.shell("Confirm Perspective Switch");
         switchShell.bot().button("Yes").click();
         assertEquals(KeYPerspective.PERSPECTIVE_ID, TestUtilsUtil.getActivePerspective().getId());
         // Select first operation contract and start proof
         SWTBotShell contractShell = bot.shell("Select Contract for Proof in KeY");
         contractShell.bot().table().select(0);
         contractShell.bot().button("OK").click();
         // Make sure that the KeY proof editor is opened
         final SWTBotEditor editor = bot.activeEditor();
         assertEquals(KeYEditor.EDITOR_ID, editor.getReference().getId());
         KeYEditor keyEditor = (KeYEditor)editor.getReference().getEditor(true);
         //check that the auto mode is available
         assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is disabled
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         //start auto mode
         TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Start Auto Mode"));
         TestUtilsUtil.waitUntilAutoMode(bot, keyEditor.getEnvironment().getUi());
         //check that auto mode is not available while auto mode is running
         assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is enabled
         assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
                  
         //stop auto mode and wait until it has stopped
         TestUtilsUtil.clickDirectly(bot.toolbarButtonWithTooltip("Stop Auto Mode"));
         TestUtilsUtil.waitWhileAutoMode(bot, keyEditor.getEnvironment().getUi());
         //make sure proof is still open
         assertFalse(keyEditor.getCurrentProof().closed());
         //check that auto mode is available again
         assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         //stop auto mode is disabled
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
      }
      finally {
         StarterPreferenceUtil.setSelectedMethodStarterID(originalStarterId);
         StarterPreferenceUtil.setDontAskForMethodStarter(originalDontAsk);
         StarterPreferenceUtil.setMethodStarterDisabled(originalDisabled);
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }
   
   /**
    * Resets the {@link SWTBotPreferences#TIMEOUT}, the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} and the open perspective.
    * Closes all shells and editors.
    * @param originalTimeout The original {@link SWTBotPreferences#TIMEOUT}.
    * @param originalSwitchPerspectivePreference The original {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE}.
    * @param originalPerspective The original perspective.
    * @param bot
    */
   private void doFinally(long originalTimeout, String originalSwitchPerspectivePreference, IPerspectiveDescriptor originalPerspective, SWTWorkbenchBot bot){
      // Restore original timeout
      SWTBotPreferences.TIMEOUT = originalTimeout;
      // Restore original switch perspective preference.
      KeYIDEPreferences.setSwitchToKeyPerspective(originalSwitchPerspectivePreference);
      // Restore original perspective
      TestUtilsUtil.openPerspective(originalPerspective);
      // close all shells
      bot.closeAllShells();
      // Close all editors
      bot.closeAllEditors();
   }
}