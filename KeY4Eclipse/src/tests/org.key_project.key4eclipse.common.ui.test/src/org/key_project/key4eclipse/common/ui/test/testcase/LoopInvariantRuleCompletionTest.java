package org.key_project.key4eclipse.common.ui.test.testcase;

import java.io.File;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.AbstractSWTBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.common.ui.util.EclipseUserInterfaceCustomization;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;

/**
 * Tests for LoopInvariantRuleCompletion
 * @author Viktor Pfanschilling
 *
 */
public class LoopInvariantRuleCompletionTest extends TestCase{
   SWTWorkbenchBot bot = null;
   SWTBotShell dialogShell = null;
   SWTBotEditor editor = null;
   
   //TODO: Automate pop up dialogs that appear
   //TODO: Cleanup.
   
   /**
    * Tests whether the finish button is inactive at the right times
    * @throws Exception 
    */
   @Test
   public void testFinishButtonInactive() throws Exception {
      setupTest("MyClass.proof");
      openLIDialog();
      dialogShell.bot().text("self.array.*").setText("There is no way *this* is a valid specification.");
      assertFalse(dialogShell.bot().button("Finish").isEnabled());
      dialogShell.bot().button("Cancel").click();
      dialogShell = null;
   }
   
   /**
    * Tests whether the finish button is active at the right times
    */
   @Test
   public void testFinishButtonActive() throws Exception {
      setupTest("LoopInvariantExample.proof");
      openLIDialog();
      //Thread.sleep(100000);
      assertTrue(dialogShell.bot().button("Finish").isEnabled());
      dialogShell.bot().button("Cancel").click();
      dialogShell = null;
   }
   
   /**
    * Tests whether completing the dialog applies the invariant
    */
   @Test
   public void testCompleteApplication() throws Exception {
      setupTest("LoopInvariantExample.proof");
      openLIDialog();
      dialogShell.bot().button("Finish").click();
      dialogShell = null;
      final SWTBotStyledText styledText = editor.bot().styledText();
      assertTrue(styledText.getText().contains("i >= 0 & i <= _array.length"));
      assertFalse(styledText.getText().contains("bogus, this isn't actually in the text."));
   }
   
   /**
    * Tests whether re-opening the dialog restores the specification
    * Currently disabled until I figure out how to prune the proof.
    */
   private void notActuallyATestRestore() throws Exception {
      setupTest("LoopInvariantExample.proof");
      openLIDialog();
      dialogShell.bot().text("i >= 0 & i <= _array.length").setText("i > -1 & i <= _array.length");
      dialogShell.bot().button("Finish").click();
      dialogShell = null;
      prune(0);
      openLIDialog();
      assertNotNull(dialogShell.bot().text("i > -1 & i <= _array.length"));
      dialogShell.bot().button("Finish").click();
      dialogShell = null;
   }
   
   /**
    * Tests whether additional heaps are displayed in the dialog
    */
   @Test
   public void testAdditionalHeaps() throws Exception {
      setupTest("MyClass.proof");
      openLIDialog();
      assertNotNull(dialogShell.bot().tabItem("permissions").activate());
      assertNotNull(dialogShell.bot().text("false"));
      dialogShell.bot().button("Cancel").click();
      dialogShell = null;
   }
   
   /**
    * sets up a test environment
    * @throws Exception
    */
   private void setupTest(String filename) throws Exception{
      // Close welcome view if available
      bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("LoopInvariantRuleCompletionTest");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/loopInvariantExample", src);
      
      final Proof proof;
      editor = null;
      // Get local file in operating system of folder src 
      File location = ResourceUtil.getLocation(src);
      File[] filesInLoc = location.listFiles();
      assertNotNull(filesInLoc);
      assertEquals(filesInLoc.length, 1);
      File proofFolder = filesInLoc[0];
      
      // Load source code in KeY and get contract to proof which is the first contract of LogRecord#getBalance().
      final KeYEnvironment<DefaultUserInterfaceControl>  environment =
            KeYEnvironment.load(new File(proofFolder, filename), null, null, null, EclipseUserInterfaceCustomization.getInstance());
      
      proof = environment.getLoadedProof();
      assertNotNull(proof);
      
      IRunnableWithException run = new AbstractRunnableWithException() {
         @Override
         public void run() {
            try {
               SWTBotShell s = bot.activeShell();
               assertNotNull(s);
               StarterUtil.openProofStarter(s.widget, proof, environment, null, true, true, true, true);
            }
            catch (Exception e) {
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
      
      AbstractSWTBot<?> eclEditor = bot.activeShell();
      assertNotNull(eclEditor);
   }
   
   private void openLIDialog(){

      //click context menu / text we're looking for: The first { should be the start of the update.
      final SWTBotStyledText styledText = editor.bot().styledText();
      Point point = TestUtilsUtil.selectText(styledText, "{");
      point = new Point(point.x-1, point.y);
      
      TestUtilsUtil.setCursorLocation(styledText, point.x, point.y);
      TestUtilsUtil.clickContextMenu(styledText, point.x, point.y, "Loop Invariant");
      SWTBotShell shell = bot.activeShell();
      
      dialogShell = shell;
   }
   
   private void prune(int node){
      SWTBotView view = null;
      for(SWTBotView viewIt : bot.views()){
         System.out.println("View title = " + viewIt.getTitle());
         if (viewIt.getTitle().equals("Outline")) {
            System.out.println("This is a match");
            view = viewIt;
         }
      }
      assertNotNull(view);
      view.bot().tree().getTreeItem("22:Loop Invariant").contextMenu("Prune Proof").click();
   }
}
