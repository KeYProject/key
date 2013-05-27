package org.key_project.keyide.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.perspectives.KeYPerspective;
import org.key_project.keyide.ui.test.Activator;
import org.key_project.keyide.ui.test.testcase.swtbot.SWTBotStartProofHandlerTest.IStartProofTestRunnable;
import org.key_project.keyide.ui.util.KeYIDEPreferences;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.MiscTools;

public class SWTBotManualRuleApplicationTest extends TestCase {
   
   @Test
   public void testCloseFalse_ProofClosed() throws CoreException, InterruptedException{
      IStartProofTestRunnable starter = new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "isValid() : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      };
      doStartProofTest("SWTBotManualRuleApplicationTest_testCloseFalse_ProofClosed", 
                       starter,
                       92,
                       28,
                       108,
                       "closeFalse",
                       true);
   }
   
   @Test
   public void testAssignment_ProofStillOpen() throws CoreException, InterruptedException{
      IStartProofTestRunnable starter = new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "isValid() : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      };
      doStartProofTest("SWTBotManualRuleApplicationTest_testAssignment_ProofStillOpen", 
                       starter,
                       0,
                       114,
                       161,
                       "assignment",
                       false);
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
                                   IStartProofTestRunnable startProofRunnable,
                                   int numOfRulesToApplyAutomatically,
                                   int x,
                                   int y,
                                   String ruleNameToApply,
                                   boolean expectedProofClosed) throws CoreException, InterruptedException {
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
         contractShell.bot().button("OK").click();
         // Test if the correct editor is opened
         SWTBotEditor editor = bot.activeEditor();
         assertEquals(KeYEditor.EDITOR_ID, editor.getReference().getId());
         // Get editor and test initial proof
         SWTBot editorBot = editor.bot();
         KeYEditor keyEditor = (KeYEditor)editor.getReference().getEditor(true);
         assertFalse(keyEditor.getCurrentProof().closed());
         // Make sure that start stop auto mode buttons are as expected
         assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
         // Start auto mode if required
         if (numOfRulesToApplyAutomatically >= 1) {
            StrategySettings ss = keyEditor.getCurrentProof().getSettings().getStrategySettings();
            ss.setMaxSteps(numOfRulesToApplyAutomatically);
            keyEditor.getEnvironment().getUi().startAndWaitForAutoMode(keyEditor.getCurrentProof());
         }
         // Get node to apply rule on
         Node node = keyEditor.getShowNode();
         assertFalse(node.isClosed());
         assertEquals(0, node.childrenCount());
         // Apply rule "assignment" interactively
         final SWTBotStyledText styledText = editorBot.styledText();
         TestUtilsUtil.setCursorLocation(styledText, x, y);
         TestUtilsUtil.clickContextMenu(styledText, x, y, ruleNameToApply);
         // Make sure that correct rule was applied
         assertEquals(expectedProofClosed, keyEditor.getCurrentProof().closed());
         assertEquals(1, node.childrenCount());
         assertEquals(ruleNameToApply, MiscTools.getRuleDisplayName(node));
         assertEquals(expectedProofClosed, node.isClosed());
         // Make sure that start stop auto mode buttons are as expected
         assertEquals(!expectedProofClosed, bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
         assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
      }
      finally {
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
}
