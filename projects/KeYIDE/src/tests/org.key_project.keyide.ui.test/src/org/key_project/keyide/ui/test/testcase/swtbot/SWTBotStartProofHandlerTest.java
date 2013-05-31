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
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.handlers.StartProofHandler;
import org.key_project.keyide.ui.perspectives.KeYPerspective;
import org.key_project.keyide.ui.test.Activator;
import org.key_project.keyide.ui.util.KeYIDEPreferences;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * <p>
 * SWTBot tests for {@link StartProofHandler}.
 * </p>
 * <p>
 * Requires the following JVM settings: -Xms128m -Xmx1024m -XX:MaxPermSize=256m
 * </p>
 * <p>
 * If you got timeout exceptions increase the waiting time with the following
 * additional JVM parameter: -Dorg.eclipse.swtbot.search.timeout=10000
 * </p>
 * @author Martin Hentschel, Niklas Bunzel
 */
public class SWTBotStartProofHandlerTest extends TestCase {
   /**
    * Tests starting of a proof via the context menu of a selected method in a JDT editor.
    */
   @Test
   public void testStartProofInEditor() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogYesTest("SWTBotStartProofHandlerTest_testStartProofInEditor", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            outlineView.setFocus();
            // Select method "charge(int) : boolean" in text editor
            SWTBotEditor editor = bot.editorByTitle(editorPart.getTitle());
            SWTBotStyledText styledText = editor.bot().styledText();
            styledText.selectRange(54, 18, 6);
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(styledText, "Start Proof");
         }
      }, "OK", KeYEditor.EDITOR_ID);
   }
   
   /**
    * Tests starting of proof via the context menu of a method ({@link IMethod}) in the outline view.
    */
   @Test
   public void testStartProofInOutline() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogYesTest("SWTBotStartProofHandlerTest_testStartProofInOutline", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in outline view
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outlineView.bot().tree();
            TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
         }
      }, "OK", KeYEditor.EDITOR_ID);
   }
   
   /**
    * Tests starting of proof via the context menu of a method ({@link IMethod}) in the project explorer.
    */
   @Test
   public void testStartProofInProjectExplorer() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogYesTest("SWTBotStartProofHandlerTest_testStartProofInProjectExplorer", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      }, "OK", KeYEditor.EDITOR_ID);
   }

   /**
    * Tests the perspective is never changed functionality by clicking the "Remember my decision" checkbox in the contract dialog.
    * First starting of a proof via the context menu of a selected method in a JDT editor.
    */
   @Test
   public void testStartProofInEditorPerspectiveNeverChanged() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogNoRememberTest("SWTBotStartProofHandlerTest_testStartProofInEditorPerspectiveNeverChanged", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            outlineView.setFocus();
            // Select method "charge(int) : boolean" in text editor
            SWTBotEditor editor = bot.editorByTitle(editorPart.getTitle());
            SWTBotStyledText styledText = editor.bot().styledText();
            styledText.selectRange(54, 18, 6);
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(styledText, "Start Proof");
         }
      }, "OK", KeYEditor.EDITOR_ID);
   }

   /**
    * Tests the perspective is never changed functionality by clicking the "Remember my decision" checkbox in the contract dialog.
    * In order to do so, it first starts a proof via the context menu of a method ({@link IMethod}) in the outline view.
    */
   @Test
   public void testStartProofInOutlinePerspectiveNeverChanged() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogNoRememberTest("SWTBotStartProofHandlerTest_testStartProofInOutlinePerspectiveNeverChanged", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in outline view
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outlineView.bot().tree();
            TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
         }
      }, "OK", KeYEditor.EDITOR_ID);
   }
   
   /**
    * Tests the perspective is never changed functionality by clicking the "Remember my decision" checkbox in the contract dialog.
    * In order to do so, it first starts a proof via the context menu of a method ({@link IMethod}) in the project explorer.
    */
   @Test
   public void testStartProofInProjectExplorerPerspectiveNeverChanged() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogNoRememberTest("SWTBotStartProofHandlerTest_testStartProofInProjectExplorerPerspectiveNeverChanged", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      }, "OK", KeYEditor.EDITOR_ID);
   }

   /**
    * Tests the perspective is always changed functionality by clicking the "Remember my decision" checkbox in the contract dialog.
    * First starting of a proof via the context menu of a selected method in a JDT editor.
    */
   @Test
   public void testStartProofInEditorPerspectiveAlwaysChanged() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogYesRememberTest("SWTBotStartProofHandlerTest_testStartProofInEditorPerspectiveAlwaysChangedPerspectiveAlwaysChanged", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
         // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            outlineView.setFocus();
            // Select method "charge(int) : boolean" in text editor
            SWTBotEditor editor = bot.editorByTitle(editorPart.getTitle());
            SWTBotStyledText styledText = editor.bot().styledText();
            styledText.selectRange(54, 18, 6);
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(styledText, "Start Proof");
         }
      }, "OK", KeYEditor.EDITOR_ID);
   }   
   
   /**
    * Tests the perspective is always changed functionality by clicking the "Remember my decision" checkbox in the contract dialog.
    * In order to do so, it first starts a proof via the context menu of a method ({@link IMethod}) in the outline view.
    */
   @Test
   public void testStartProofInOutlinePerspectiveAlwaysChanged() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogYesRememberTest("SWTBotStartProofHandlerTest_testStartProofInOutlinePerspectiveAlwaysChanged", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
         // Select method "charge(int) : boolean" in outline view
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outlineView.bot().tree();
            TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
         }
      }, "OK", KeYEditor.EDITOR_ID);
   }
   
   
   /**
    * Tests the perspective is always changed functionality by clicking the "Remember my decision" checkbox in the contract dialog.
    * In order to do so, it first starts a proof via the context menu of a method ({@link IMethod}) in the project explorer.
    */
   @Test
   public void testStartProofInProjectExplorerPerspectiveAlwaysChanged() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogYesRememberTest("SWTBotStartProofHandlerTest_testStartProofInProjectExplorerPerspectiveAlwaysChanged", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      }, "OK", KeYEditor.EDITOR_ID);
   }
         
   
   /**
    * Tests starting of a proof via the context menu of a selected method in a JDT editor, without the "Confirm perspective switch" dialog.
    * By setting the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "always".
    * @throws InterruptedException 
    * @throws CoreException 
    */
   public void testSetPerspectiveChangedPreferencesAlwaysStartProofInEditor() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testSetPerspectiveChangedPreferencesAlwaysStartProofInEditor", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            outlineView.setFocus();
            // Select method "charge(int) : boolean" in text editor
            SWTBotEditor editor = bot.editorByTitle(editorPart.getTitle());
            SWTBotStyledText styledText = editor.bot().styledText();
            styledText.selectRange(54, 18, 6);
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(styledText, "Start Proof");
         }
      }, "OK", MessageDialogWithToggle.ALWAYS, KeYEditor.EDITOR_ID);
   }
   
   /**
    * Tests starting of a proof via the context menu of a method ({@link IMethod}) in the outline view, without the "Confirm perspective switch" dialog.
    * By setting the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "always".
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testSetPerspectiveChangedPreferencesAlwaysStartProofInOutline() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testSetPerspectiveChangedPreferencesAlwaysStartProofInOutline", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in outline view
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outlineView.bot().tree();
            TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
         }
      }, "OK", MessageDialogWithToggle.ALWAYS, KeYEditor.EDITOR_ID);
   }
   
   /**
    * Tests starting of a proof via the context menu of a method ({@link IMethod}) in the project explorer, without the "Confirm perspective switch" dialog.
    * By setting the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "always".
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testSetPerspectiveChangedPreferencesAlwaysStartProofInProjectExplorer() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testSetPerspectiveChangedPreferencesAlwaysStartProofInProjectExplorer", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      }, "OK", MessageDialogWithToggle.ALWAYS, KeYEditor.EDITOR_ID);
      
   }
   
   /**
    * Tests starting of a proof via the context menu of a selected method in a JDT editor, without the "Confirm perspective switch" dialog.
    * By setting the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "never".
    * @throws InterruptedException 
    * @throws CoreException 
    */
   public void testSetPerspectiveChangedPreferencesNeverStartProofInEditor() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testSetPerspectiveChangedPreferencesNeverStartProofInEditor", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            outlineView.setFocus();
            // Select method "charge(int) : boolean" in text editor
            SWTBotEditor editor = bot.editorByTitle(editorPart.getTitle());
            SWTBotStyledText styledText = editor.bot().styledText();
            styledText.selectRange(54, 18, 6);
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(styledText, "Start Proof");
         }
      }, "OK", MessageDialogWithToggle.NEVER, KeYEditor.EDITOR_ID);
   }
   
   /**
    * Tests starting of a proof via the context menu of a method ({@link IMethod}) in the outline view, without the "Confirm perspective switch" dialog.
    * By setting the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "never".
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testSetPerspectiveChangedPreferencesNeverStartProofInOutline() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testSetPerspectiveChangedPreferencesNeverStartProofInOutline", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in outline view
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outlineView.bot().tree();
            TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
         }
      }, "OK", MessageDialogWithToggle.NEVER, KeYEditor.EDITOR_ID);
   }
   
   /**
    * Tests starting of a proof via the context menu of a method ({@link IMethod}) in the project explorer, without the "Confirm perspective switch" dialog.
    * By setting the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "never".
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testSetPerspectiveChangedPreferencesNeverStartProofInProjectExplorer() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testSetPerspectiveChangedPreferencesNeverStartProofInProjectExplorer", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      }, "OK", MessageDialogWithToggle.NEVER, KeYEditor.EDITOR_ID);
      
   }
   
   /**
    * Tests canceling the proof in the contract dialog.
    * In order to do so it first sets the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "always"
    * and starts a proof via the context menu of a selected method in a JDT editor.
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testCancelProofPerspectiveChangedPreferencesAlwaysStartProofInEditor() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testCancelProofPerspectiveChangedPreferencesAlwaysStartProofInEditor", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            outlineView.setFocus();
            // Select method "charge(int) : boolean" in text editor
            SWTBotEditor editor = bot.editorByTitle(editorPart.getTitle());
            SWTBotStyledText styledText = editor.bot().styledText();
            styledText.selectRange(54, 18, 6);
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(styledText, "Start Proof");
         }
      }, "Cancel", MessageDialogWithToggle.ALWAYS, "org.eclipse.jdt.ui.CompilationUnitEditor");
   }
   
   /**
    * Tests canceling the proof in the contract dialog.
    * In order to do so it first sets the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "always"
    * and starts a proof via the context menu of a method ({@link IMethod}) in the outline view. 
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testCancelProofPerspectiveChangedPreferencesAlwaysStartProofInOutline() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testCancelProofPerspectiveChangedPreferencesAlwaysStartProofInOutline", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in outline view
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outlineView.bot().tree();
            TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
         }
      }, "Cancel", MessageDialogWithToggle.ALWAYS, "org.eclipse.jdt.ui.CompilationUnitEditor");
   }
   
   /**
    * Tests canceling the proof in the contract dialog.
    * In order to do so it first sets the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "always"
    * and starts a proof via the context menu of a method ({@link IMethod}) in the project explorer. 
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testCancelProofPerspectiveChangedPreferencesAlwaysStartProofInProjectExplorer() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testCancelProofPerspectiveChangedPreferencesAlwaysStartProofInProjectExplorer", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      }, "Cancel", MessageDialogWithToggle.ALWAYS, "org.eclipse.jdt.ui.CompilationUnitEditor");
      
   }
   
   /**
    * Tests canceling the proof in the contract dialog.
    * In order to do so it first sets the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "never"
    * and starts a proof via the context menu of a selected method in a JDT editor.
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testCancelProofPerspectiveChangedPreferencesNeverStartProofInEditor() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testCancelProofPerspectiveChangedPreferencesNeverStartProofInEditor", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            outlineView.setFocus();
            // Select method "charge(int) : boolean" in text editor
            SWTBotEditor editor = bot.editorByTitle(editorPart.getTitle());
            SWTBotStyledText styledText = editor.bot().styledText();
            styledText.selectRange(54, 18, 6);
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(styledText, "Start Proof");
         }
      }, "Cancel", MessageDialogWithToggle.NEVER, "org.eclipse.jdt.ui.CompilationUnitEditor");
   }
   
   /**
    * Tests canceling the proof in the contract dialog.
    * In order to do so it first sets the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "never"
    * and starts a proof via the context menu of a method ({@link IMethod}) in the outline view. 
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testCancelProofPerspectiveChangedPreferencesNeverStartProofInOutline() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testCancelProofPerspectiveChangedPreferencesNeverStartProofInOutline", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in outline view
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outlineView.bot().tree();
            TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
         }
      }, "Cancel", MessageDialogWithToggle.NEVER, "org.eclipse.jdt.ui.CompilationUnitEditor");
   }
   
   /**
    * Tests canceling the proof in the contract dialog.
    * In order to do so it first sets the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE} to "always"
    * and starts a proof via the context menu of a method ({@link IMethod}) in the project explorer. 
    * @throws InterruptedException 
    * @throws CoreException
    */
   public void testCancelProofPerspectiveChangedPreferencesNeverStartProofInProjectExplorer() throws CoreException, InterruptedException{
      doStartProofWithoutSwitchToPerspectiveDialogTest("SWTBotStartProofHandlerTest_testCancelProofPerspectiveChangedPreferencesNeverStartProofInProjectExplorer", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      }, "Cancel", MessageDialogWithToggle.NEVER, "org.eclipse.jdt.ui.CompilationUnitEditor");
   
   }
   
   /**
    * Tests canceling the proof in the contract dialog.
    * First starting the proof via the context menu of a selected method in a JDT editor.
    */
   @Test
   public void testCancelProofInEditor() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogYesTest("SWTBotStartProofHandlerTest_testCancelProofInEditor", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            outlineView.setFocus();
            // Select method "charge(int) : boolean" in text editor
            SWTBotEditor editor = bot.editorByTitle(editorPart.getTitle());
            SWTBotStyledText styledText = editor.bot().styledText();
            styledText.selectRange(54, 18, 6);
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(styledText, "Start Proof");
         }
      }, "Cancel", "org.eclipse.jdt.ui.CompilationUnitEditor");
   }
   
   /**
    * Tests canceling the proof in the contract dialog.
    * First starting the proof via the context menu of a method ({@link IMethod}) in the outline view.
    */
   @Test
   public void testCancelProofInOutline() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogYesTest("SWTBotStartProofHandlerTest_testCancelProofInOutline", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in outline view
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outlineView.bot().tree();
            TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
         }
      }, "Cancel", "org.eclipse.jdt.ui.CompilationUnitEditor");
   }
   
   /**
    * Tests canceling the proof in the contract dialog.
    * First starting the proof via the context menu of a method ({@link IMethod}) in the project explorer.
    */
   @Test
   public void testCancelProofInProjectExplorer() throws CoreException, InterruptedException {
      doStartProofSwitchPerspectiveDialogYesTest("SWTBotStartProofHandlerTest_testCancelProofInProjectExplorer", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      }, "Cancel", "org.eclipse.jdt.ui.CompilationUnitEditor");
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
   
   /**
    * Sets the switchToKeYPerspective from the {@link KeYIDEPreferences} and than
    * executes the test steps of
    * {@link #testStartProofInEditorPerspectiveAlwaysChanged()},
    * {@link #testStartProofInEditorPerspectiveNeverChanged()},
    * {@link #testStartProofInOutlinePerspectiveAlwaysChanged()},
    * {@link #testStartProofInOutlinePerspectiveNeverChanged()},
    * {@link #testStartProofInProjectExplorerPerspectiveAlwaysChanged()} and
    * {@link #testStartProofInProjectExplorerPerspectiveNeverChanged()}.
    * @param projectName The name of the project to create and to extract test files to.
    * @param startProofRunnable The {@link IStartProofTestRunnable} which is executed to start a proof.
    * @param contractButton The contract button to click. "OK" or "Cancel".
    * @param switchToPerspective The value to set the {@link KeYIDEPreferences#SWITCH_TO_KEY_PERSPECTIVE}.
    * @param expectedEditor The editor id of the editor you expect to be opened.
    * @throws CoreException
    * @throws InterruptedException
    */
   protected void doStartProofWithoutSwitchToPerspectiveDialogTest(String projectName, 
                                                                   IStartProofTestRunnable startProofRunnable, 
                                                                   String contractButton, 
                                                                   String switchToPerspective, 
                                                                   String expectedEditor) throws CoreException, InterruptedException {
      // Make sure that given parameters are valid.
      assertNotNull(startProofRunnable);
      assertNotNull(projectName);
      assertTrue(!projectName.isEmpty());
      assertTrue(MessageDialogWithToggle.ALWAYS.equals(switchToPerspective) || 
                 MessageDialogWithToggle.PROMPT.equals(switchToPerspective) || 
                 MessageDialogWithToggle.NEVER.equals(switchToPerspective));
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 5;
      // Backup original switch perspective preference.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      //set switchToPerspective
      KeYIDEPreferences.setSwitchToKeyPerspective(switchToPerspective);
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
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
         // Select first operation contract and start proof
         SWTBotShell contractShell = bot.shell("Select Contract for Proof in KeY");
         contractShell.bot().table().select(0);
         contractShell.bot().button(contractButton).click();
         // Test if the correct editor is opened
         SWTBotEditor editor = bot.activeEditor();
         assertEquals(expectedEditor, editor.getReference().getId());
//         assertEquals(KeYIDEPreferences.SWITCH_TO_KEY_PERSPECTIVE, switchToPerspective);
      }
      finally {
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }
   
   
   /**
    * Executes the test steps of
    * {@link #testStartProofInEditor()},
    * {@link #testStartProofInOutline()} and
    * {@link #testStartProofInProjectExplorer()}.
    * @param projectName The name of the project to create and to extract test files to.
    * @param startProofRunnable The {@link IStartProofTestRunnable} which is executed to start a proof.
    * @param contractButton The contract button to click. "OK" or "Cancel".
    * @param expectedEditor The editor id of the editor you expect to be opened.
    * @throws CoreException Occurred Exception.
    * @throws InterruptedException Occurred Exception.
    */
   protected void doStartProofSwitchPerspectiveDialogYesTest(String projectName, 
                                   IStartProofTestRunnable startProofRunnable, String contractButton, String expectedEditor) throws CoreException, InterruptedException {
      // Make sure that given parameters are valid.
      assertNotNull(startProofRunnable);
      assertNotNull(projectName);
      assertTrue(!projectName.isEmpty());
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 5;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
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
         contractShell.bot().button(contractButton).click();
         // Test if the correct editor is opened
         SWTBotEditor editor = bot.activeEditor();
         assertEquals(expectedEditor, editor.getReference().getId());
         }
      finally {
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }
   
   /**
    * Executes the test steps of
    * {@link #testStartProofInEditor()},
    * {@link #testStartProofInOutline()} and
    * {@link #testStartProofInProjectExplorer()}.
    * @param projectName The name of the project to create and to extract test files to.
    * @param startProofRunnable The {@link IStartProofTestRunnable} which is executed to start a proof.
    * @param contractButton The contract button to click. "OK" or "Cancel".
    * @param expectedEditor The editor id of the editor you expect to be opened.
    * @throws CoreException Occurred Exception.
    * @throws InterruptedException Occurred Exception.
    */
   protected void doStartProofSwitchPerspectiveDialogYesRememberTest(String projectName, 
                                   IStartProofTestRunnable startProofRunnable, String contractButton, String expectedEditor) throws CoreException, InterruptedException {
      // Make sure that given parameters are valid.
      assertNotNull(startProofRunnable);
      assertNotNull(projectName);
      assertTrue(!projectName.isEmpty());
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 5;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
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
         //set Remember decision
         switchShell.bot().checkBox("Remember my decision").click();
         switchShell.bot().button("Yes").click();
         // tests if KeY Preference is set
         assertEquals(MessageDialogWithToggle.ALWAYS, KeYIDEPreferences.getSwitchToKeyPerspective());
         assertEquals(KeYPerspective.PERSPECTIVE_ID, TestUtilsUtil.getActivePerspective().getId());
         // Select first operation contract and start proof
         SWTBotShell contractShell = bot.shell("Select Contract for Proof in KeY");
         contractShell.bot().table().select(0);
         contractShell.bot().button(contractButton).click();
         // Test if the correct editor is opened
         SWTBotEditor editor = bot.activeEditor();
         assertEquals(expectedEditor, editor.getReference().getId());
         }
      finally {
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }
   
   /**
    * Executes the test steps of
    * {@link #testStartProofInEditor()},
    * {@link #testStartProofInOutline()} and
    * {@link #testStartProofInProjectExplorer()}.
    * @param projectName The name of the project to create and to extract test files to.
    * @param startProofRunnable The {@link IStartProofTestRunnable} which is executed to start a proof.
    * @param contractButton The contract button to click. "OK" or "Cancel".
    * @param expectedEditor The editor id of the editor you expect to be opened.
    * @throws CoreException Occurred Exception.
    * @throws InterruptedException Occurred Exception.
    */
   protected void doStartProofSwitchPerspectiveDialogNoRememberTest(String projectName, 
                                   IStartProofTestRunnable startProofRunnable, String contractButton, String expectedEditor) throws CoreException, InterruptedException {
      // Make sure that given parameters are valid.
      assertNotNull(startProofRunnable);
      assertNotNull(projectName);
      assertTrue(!projectName.isEmpty());
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 5;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
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
         //set Remember decision
         switchShell.bot().checkBox("Remember my decision").click();
         switchShell.bot().button("No").click();
         // tests if KeY Preference is set
         assertEquals(MessageDialogWithToggle.NEVER, KeYIDEPreferences.getSwitchToKeyPerspective());
         assertEquals(originalPerspective.getId(), TestUtilsUtil.getActivePerspective().getId());
         // Select first operation contract and start proof
         SWTBotShell contractShell = bot.shell("Select Contract for Proof in KeY");
         contractShell.bot().table().select(0);
         contractShell.bot().button(contractButton).click();
         // Test if the correct editor is opened
         SWTBotEditor editor = bot.activeEditor();
         assertEquals(expectedEditor, editor.getReference().getId());
         }
      finally {
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }
   
   
   /**
    * Utility runnable which is used to start a proof.
    * @author Martin Hentschel
    */
   protected static interface IStartProofTestRunnable {
      /**
       * Starts a proof.
       * @param projectName The name of the project which contains the test files.
       * @param bot The used {@link SWTWorkbenchBot}.
       * @param editorPart The currently opened editor.
       */
      public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart);
   }
}
