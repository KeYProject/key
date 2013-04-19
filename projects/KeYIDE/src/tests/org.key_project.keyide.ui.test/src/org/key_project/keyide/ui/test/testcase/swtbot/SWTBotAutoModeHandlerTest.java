package org.key_project.keyide.ui.test.testcase.swtbot;

import java.io.File;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jface.dialogs.MessageDialogWithToggle;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.handlers.HandlerUtil;
import org.junit.Test;
import org.key_project.keyide.ui.editor.IProofEnvironmentProvider;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.handlers.StartAutoModeHandler;
import org.key_project.keyide.ui.handlers.StartProofHandler;
import org.key_project.keyide.ui.perspectives.KeYPerspective;
import org.key_project.keyide.ui.test.Activator;
import org.key_project.keyide.ui.test.testcase.swtbot.SWTBotStartProofHandlerTest.IStartProofTestRunnable;
import org.key_project.keyide.ui.util.KeYIDEUtil;
import org.key_project.keyide.ui.util.KeYIDEPreferences;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.ProblemLoaderException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.ui.UserInterface;


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
public class SWTBotAutoModeHandlerTest extends TestCase{

   
   /**
    * Tests starting the auto mode.
    * @throws ProblemLoaderException 
    */
   @Test
   public void testStartAutoMode() throws CoreException, InterruptedException, ProblemLoaderException {
      String projectName = "SWTBotStartAutoModeHandlerTest_testStartAutoMode";
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
         
         
         
         Display.getDefault().asyncExec(new Runnable() {
            @Override
            public void run() {
               //check that the auto mode is available
               assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
               //stop auto mode is disabled
               assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
               //start auto mode
               bot.toolbarButtonWithTooltip("Start Auto Mode").click();
               
               
               
               //check that auto mode is not available while auto mode is running
               assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
               //stop auto mode is enabled
               assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            }
         });
         
         
      }
      finally {
         doFinally(originalTimeout, originalSwitchPerspectivePreference, originalPerspective, bot);
      }
   }
   
   @Test
   public void testStopAutoMode() throws CoreException, InterruptedException, ProblemLoaderException{
      String projectName = "SWTBotStopAutoModeHandlerTest_testStartAutoMode";
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
         
         Display.getDefault().asyncExec(new Runnable() {
            @Override
            public void run() {
                //check that the auto mode is available
                  assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
                  //stop auto mode is disabled
                  assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
                  //start auto mode
                  bot.toolbarButtonWithTooltip("Start Auto Mode").click();
                  //check that auto mode is not available while auto mode is running
                  assertFalse(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
                  //stop auto mode is enabled
                  assertTrue(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
                  
                  //stop auto mode
                  bot.toolbarButtonWithTooltip("Stop Auto Mode").click();
                  //check that auto mode is available again
                  assertTrue(bot.toolbarButtonWithTooltip("Start Auto Mode").isEnabled());
                  //stop auto mode is disabled
                  assertFalse(bot.toolbarButtonWithTooltip("Stop Auto Mode").isEnabled());
            }
         });
         
         
      }
      finally {
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
