package org.key_project.keyide.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.SWTBotWidget;
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

public class SWTBotManualRuleApplication extends TestCase {
   
   @Test
   public void testEverything() throws CoreException, InterruptedException{
      doStartProofTest("SWTBotStartProofHandlerTest_testStartProofInProjectExplorerPerspectiveAlwaysChanged", new IStartProofTestRunnable() {
         @Override
         public void startProof(String projectName, SWTWorkbenchBot bot, IEditorPart editorPart) {
            // Select method "charge(int) : boolean" in project explorer
            SWTBotView projectView = TestUtilsUtil.getProjectExplorer(bot);
            SWTBotTree projectTree = projectView.bot().tree();
            TestUtilsUtil.selectInTree(projectTree, projectName, "src", "(default package)", "PayCard.java", "PayCard", "isValid() : boolean");
            // Start proof via context menu
            TestUtilsUtil.clickContextMenu(projectTree, "Start Proof");
         }
      });
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
         
         //----------------------------->>>>>>>>>>>>>>>>>>>>>>>><<
         // Set focus to outline view because otherwise the context menu of the editor does not contain the "Start Proof" menu item
//         SWTBotView outlineView = TestUtilsUtil.getOutlineView(bot);
//         outlineView.setFocus();
         SWTBot editorBot = editor.bot();
         SWTBotStyledText styledText = editorBot.styledText();
         
         //styledText.selectRange(103, 27, 7);
         // apply rule via context menu
         //System.out.println(styledText.getTextOnLine(9));
         styledText.selectLine(9);
//         System.out.println(styledText.cursorPosition());
//         styledText.setFocus();
//         System.out.println(styledText.cursorPosition());
//         styledText.navigateTo(9, 17);
//         System.out.println(styledText.cursorPosition());
//         styledText.selectRange(9, 0, 19);
//         System.out.println(styledText.cursorPosition());

//         try{
//            editorBot.menu("diamond_split_termination");
//         }catch(Exception e){
//            System.out.println("menu");
//         }
//         try{
//         styledText.contextMenu("diamond_split_termination");
//         }catch(Exception e){
//            System.out.println("diamond");
//         }
//         try{
//         TestUtilsUtil.clickContextMenu(styledText, "diamond_split_termination");
//         }catch(Exception e){
//            System.out.println("TestUtilsUtil.clickContextMenu(styledText, exec=null)");
//         }
//         try{
//            editorBot.activeShell().contextMenu("diamond_split_termination");
//         }catch(Exception e){
//            System.out.println("editorBot.activeshell.contextmenu");
//         }
//         try{
//            editorBot.browser().contextMenu("diamond_split_termination");
//         }catch(Exception e){
//            System.out.println("editorBot.activeshell.contextmenu");
//         }
         try{
            editor.getWidget().notifyListeners(SWT.MouseMove, new Event());
         }catch(Exception e){
            System.out.println("1. notify mouse move editorBot.activeshell.contextmenu");
         }
         }
      finally {
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }

}
