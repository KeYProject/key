package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import java.io.File;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotPerspective;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.common.ui.util.EclipseUserInterfaceCustomization;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.keyide.ui.perspectives.KeYPerspective;
import org.key_project.keyide.ui.starter.KeYIDEProofStarter;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

/**
 * Tests for LoopInvariantRuleCompletion.
 * @author Viktor Pfanschilling
 *
 */
public class SWTBotLoopInvariantRuleCompletionTest extends TestCase {
   /**
    * The workbench bot this test uses.
    */
   private SWTWorkbenchBot bot = null;
   /**
    * The shell of the LoopInvariant dialog under Test.
    */
   private SWTBotShell dialogShell = null;
   /**
    * The editor used to open the above dialog.
    */
   private SWTBotEditor editor = null;
   /**
    * The previous Eclipse perspective, stored to restore.
    */
   private SWTBotPerspective previousperspective = null;
   /**
    * The previous proofStarter, stored to restore.
    */
   private String prevProofStarter = null;
   /**
    * The previous dontAsk setting, stored to restore.
    */
   private boolean prevDontAsk = false;
   /**
    * The Proof used for the test.
    */
   private Proof proof = null;
   /**
    * The KeY Environment.
    */
   private KeYEnvironment<DefaultUserInterfaceControl> environment = null;
   
   /**
    * Tests whether the finish button is inactive at the right times.
    * @throws Exception 
    */
   @Test
   public final void testFinishButtonInactive() throws Exception {
      try {
         setupTest("MyClass.proof");
         openLIDialog("Loop Invariant");
         dialogShell.bot().text("self.array.*").setText("There is no way *this* is a valid specification.");
         assertFalse(dialogShell.bot().button("Finish").isEnabled());
         dialogShell.bot().button("Cancel").click();
         dialogShell = null;
      } finally {
         restore();
      }
   }
   
   /**
    * Tests whether the finish button is active at the right times.
    * @throws Exception
    */
   @Test
   public final void testFinishButtonActive() throws Exception {
      try {
         setupTest("LoopInvariantExample.proof");
         openLIDialog("Loop Invariant");
         assertTrue(dialogShell.bot().button("Finish").isEnabled());
         dialogShell.bot().button("Cancel").click();
         dialogShell = null;
      } finally {
         restore();
      }
   }
   
   /**
    * Tests whether completing the dialog applies the invariant.
    */
   @Test
   public final void testCompleteApplication() throws Exception {
      try {
         setupTest("LoopInvariantExample.proof");
         openLIDialog("Loop Invariant");
         dialogShell.bot().button("Finish").click();
         dialogShell = null;
         boolean contained = false;
         for(Goal g : proof.openGoals()){
            if (g.toString().contains("i >= 0 & i <= _array.length")){
               contained = true;
            }
            assertFalse(proof.openGoals().head().toString().contains("bogus, this isn't actually in the text."));
         }
         assertTrue(contained);
      } finally {
         restore();
      }
   }
   
   /**
    * Tests whether additional heaps are displayed in the dialog.
    */
   @Test
   public final void testAdditionalHeaps() throws Exception {
      try {
         setupTest("MyClass.proof");
         openLIDialog("Loop Invariant");
         assertNotNull(dialogShell.bot().tabItem("permissions").activate());
         assertNotNull(dialogShell.bot().text("false"));
         dialogShell.bot().button("Cancel").click();
         dialogShell = null;
      } finally {
         restore();
      }
   }
   
   /**
    * restores the initial conditions.
    */
   private void restore() {
      if (dialogShell != null) {
         dialogShell.close();
         dialogShell = null;
      }
      previousperspective.activate();
      StarterPreferenceUtil.setDontAskForProofStarter(prevDontAsk);
      StarterPreferenceUtil.setSelectedProofStarterID(prevProofStarter);
      bot.closeAllEditors();
      if (editor != null) {
         editor.close();
      }
      if (proof != null && !proof.isDisposed()) {
         proof.dispose();
      }
      if (environment != null) {
         environment.dispose();
      }
   }
   
   /**
    * sets up a test environment.
    * @param filename The filename of the .proof file
    * @throws Exception
    */
   private void setupTest(String filename) throws Exception {
      // Close welcome view if available
      bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      
      //Don't show the dialogs inquiring about starters and perspectives. Store defaults for restore()
      previousperspective = bot.activePerspective();
      bot.perspectiveById(KeYPerspective.PERSPECTIVE_ID).activate();
      prevProofStarter = StarterPreferenceUtil.getSelectedProofStarterID();
      StarterPreferenceUtil.setSelectedProofStarterID(KeYIDEProofStarter.STARTER_ID);
      prevDontAsk = StarterPreferenceUtil.isDontAskForProofStarter();
      StarterPreferenceUtil.setDontAskForProofStarter(true);
      
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("LoopInvariantRuleCompletionTest");
      IFolder src = project.getProject().getFolder(JDTUtil.getSourceFolderName());
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/loopInvariantExample", src);
      
      editor = null;
      // Get local file in operating system of folder src 
      File location = ResourceUtil.getLocation(src);
      File[] filesInLoc = location.listFiles();
      assertNotNull(filesInLoc);
      assertEquals(filesInLoc.length, 1);
      File proofFolder = filesInLoc[0];
      
      
      // Load source code in KeY and get contract to proof which is the first contract of LogRecord#getBalance().
      environment = KeYEnvironment.load(
            new File(proofFolder, filename),
            null, null, null,
            EclipseUserInterfaceCustomization.getInstance());
      
      //Alternative call to Load - breaks test cases that are based on MyClass.proof
      /*environment = KeYEnvironment.load(
            SymbolicExecutionJavaProfile.getDefaultInstance(false), 
            new File(proofFolder, filename),
            null, null, null, SymbolicExecutionTreeBuilder.createPoPropertiesToForce(),
            EclipseUserInterfaceCustomization.getInstance(), true);//*/
      
      proof = environment.getLoadedProof();
      assertNotNull(proof);
      
      IRunnableWithException run = new AbstractRunnableWithException() {
         @Override
         public void run() {
            try {
               SWTBotShell s = bot.activeShell();
               assertNotNull(s);
               StarterUtil.openProofStarter(s.widget, proof, environment, null, true, true, true, true);
            } catch (Exception e) {
               setException(e);
            }
         }
      };
      
      Display.getDefault().syncExec(run);
      if (run.getException() != null) {
         throw run.getException();
      }
      editor = bot.activeEditor();
      assertNotNull(editor);
   }
   
   /**
    * opens a LoopInvariant Dialog.
    * @param rule The name of the rule to be applied - usually "Loop Invariant"
    */
   private void openLIDialog(String rule) {
      //click context menu / text we're looking for: The first { should be the start of the update.
      final SWTBotStyledText styledText = editor.bot().styledText();
      Point point = TestUtilsUtil.selectText(styledText, "{");
      point.x = point.x - 1;
      
      TestUtilsUtil.setCursorLocation(styledText, point.x, point.y);
      TestUtilsUtil.clickContextMenu(styledText, point.x, point.y, rule);
      SWTBotShell shell = bot.activeShell();
      
      dialogShell = shell;
   }
}
