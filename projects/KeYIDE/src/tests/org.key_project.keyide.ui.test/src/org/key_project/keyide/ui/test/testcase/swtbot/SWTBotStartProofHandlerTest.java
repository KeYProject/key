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
 * @author Martin Hentschel
 */
// TODO: Implement test in which the perspective is never changed
// TODO: Implement test in which the perspective is always changed
public class SWTBotStartProofHandlerTest extends TestCase {
   /**
    * Tests starting of a proof via the context menu of a selected method in a JDT editor.
    */
   @Test
   public void testStartProofInEditor() throws CoreException, InterruptedException {
      doStartProofTest("SWTBotStartProofHandlerTest_testStartProofInEditor", new IStartProofTestRunnable() {
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
      });
   }
   
   /**
    * Tests starting of proof via the context menu of a method ({@link IMethod}) in the outline view.
    */
   @Test
   public void testStartProofInOutline() throws CoreException, InterruptedException {
      doStartProofTest("SWTBotStartProofHandlerTest_testStartProofInOutline", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in outline view
            SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
            SWTBotTree outlineTree = outlineView.bot().tree();
            TestUtilsUtil.selectInTree(outlineTree, "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(outlineTree, "Start Proof");
         }
      });
   }
   
   /**
    * Tests starting of proof via the context menu of a method ({@link IMethod}) in the project explorer.
    */
   @Test
   public void testStartProofInProjectExplorer() throws CoreException, InterruptedException {
      doStartProofTest("SWTBotStartProofHandlerTest_testStartProofInProjectExplorer", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "charge(int) : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      });
   }
   
   /**
    * Executes the test steps of
    * {@link #testStartProofInEditor()},
    * {@link #testStartProofInOutline()} and
    * {@link #testStartProofInProjectExplorer()}.
    * @param projectName The name of the project to create and to extract test files to.
    * @param startProofRunnable The {@link IStartProofTestRunnable} which is executed to start a proof.
    * @throws CoreException Occurred Exception.
    * @throws InterruptedException Occurred Exception.
    */
   protected void doStartProofTest(String projectName, 
                                   IStartProofTestRunnable startProofRunnable) throws CoreException, InterruptedException {
      // Make sure that given parameters are valid.
      assertNotNull(startProofRunnable);
      assertNotNull(projectName);
      assertTrue(!projectName.isEmpty());
      // Store original SWTBot timeout and increase it
      long originalTimeout = SWTBotPreferences.TIMEOUT;
      SWTBotPreferences.TIMEOUT = originalTimeout * 4;
      // Backup original switch perspective preference and set preference to test.
      String originalSwitchPerspectivePreference = KeYIDEPreferences.getSwitchToKeyPerspective();
      KeYIDEPreferences.setSwitchToKeyPerspective(MessageDialogWithToggle.PROMPT);
      // Backup current perspective
      IPerspectiveDescriptor originalPerspective = TestUtilsUtil.getActivePerspective();
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
         // Switch to KeY perspective
         SWTBotShell switchShell = bot.shell("Confirm Perspective Switch");
         switchShell.bot().button("Yes").click();
         assertEquals(KeYPerspective.PERSPECTIVE_ID, TestUtilsUtil.getActivePerspective().getId());
         // Select first operation contract and start proof
         SWTBotShell contractShell = bot.shell("Select Contract for Proof in KeY");
         contractShell.bot().table().select(0);
         contractShell.bot().button("OK").click();
         // Make sure that the KeY proof editor is opened
         SWTBotEditor editor = bot.activeEditor();
         assertEquals(KeYEditor.EDITOR_ID, editor.getReference().getId());
      }
      finally {
         // Restore original timeout
         SWTBotPreferences.TIMEOUT = originalTimeout;
         // Restore original switch perspective preference.
         KeYIDEPreferences.setSwitchToKeyPerspective(originalSwitchPerspectivePreference);
         // Restore original perspective
         TestUtilsUtil.openPerspective(originalPerspective);
         // Close all editors
         bot.closeAllEditors();
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