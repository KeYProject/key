package org.key_project.key4eclipse.common.ui.test.testcase;

import java.io.File;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotPerspective;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.AbstractSWTBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.test.Activator;
import org.key_project.key4eclipse.common.ui.util.EclipseUserInterfaceCustomization;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * Tests for LoopInvariantRuleCompletion
 * @author Viktor Pfanschilling
 *
 */
public class LoopInvariantRuleCompletionTest extends TestCase {
   private SWTWorkbenchBot bot = null;
   private SWTBotShell dialogShell = null;
   private SWTBotEditor editor = null;
   private SWTBotPerspective previousperspective = null;
   private String prevProofStarter = null;
   private boolean prevDontAsk = false;
   private Proof proof = null;
   private KeYEnvironment<DefaultUserInterfaceControl> environment = null;
   
   /**
    * Tests whether the finish button is inactive at the right times.
    * @throws Exception 
    */
   @Test
   public final void testFinishButtonInactive() throws Exception {
      try {
         setupTest("MyClass.proof");
         openLIDialog();
         dialogShell.bot().text("self.array.*").setText("There is no way *this* is a valid specification.");
         assertFalse(dialogShell.bot().button("Finish").isEnabled());
         dialogShell.bot().button("Cancel").click();
         dialogShell = null;
      } finally {
         
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
         openLIDialog();
         assertTrue(dialogShell.bot().button("Finish").isEnabled());
         dialogShell.bot().button("Cancel").click();
         dialogShell = null;
      } finally {
         
      }
   }
   
   /**
    * Tests whether completing the dialog applies the invariant.
    */
   @Test
   public final void testCompleteApplication() throws Exception {
      try {
         setupTest("LoopInvariantExample.proof");
         openLIDialog();
         dialogShell.bot().button("Finish").click();
         dialogShell = null;
         final SWTBotStyledText styledText = editor.bot().styledText();
         assertTrue(styledText.getText().contains("i >= 0 & i <= _array.length"));
         assertFalse(styledText.getText().contains("bogus, this isn't actually in the text."));
      } finally {
         restore();
      }
   }
   
   /**
    * Tests whether re-opening the dialog restores the specification.
    * Currently disabled until I figure out how to prune the proof.
    */
   @Test
   public void testRestore() throws Exception {
      try {
         setupTest("LoopInvariantExample.proof");
         Node n = proof.root();
         //Not sure if this results in the right node.
         //If not, clickContextMenu will raise a WidgetNotFound Exception.
         while(!n.child(0).leaf()){
            n = n.child(0);
         }
         
         //Open Dialog, apply modified Invariant
         openLIDialog();
         dialogShell.bot().text("i >= 0 & i <= _array.length").setText("i > -1 & i <= _array.length");
         dialogShell.bot().button("Finish").click();
         dialogShell = null;
         
         //prune away the change.
         //"n, true" results in Exceptions, "n, false" results in no change being detected.
         proof.pruneProof(n, false);
         
         editor.setFocus();
         final SWTBotStyledText styledText = editor.bot().styledText();
         Point point = TestUtilsUtil.selectText(styledText, "{");
         point = new Point(point.x - 1, point.y);
         
         TestUtilsUtil.setCursorLocation(styledText, point.x, point.y);
         TestUtilsUtil.clickContextMenu(styledText, point.x, point.y, "gibberish");
         SWTBotShell shell = bot.activeShell();
         
         dialogShell = shell;
         
         assertNotNull(dialogShell.bot().text("i > -1 & i <= _array.length"));
         dialogShell.bot().button("Finish").click();
         dialogShell = null;
      } finally {
         restore();
      }
   }
   
   /**
    * Tests whether additional heaps are displayed in the dialog.
    */
   @Test
   public void testAdditionalHeaps() throws Exception {
      try {
         setupTest("MyClass.proof");
         openLIDialog();
         assertNotNull(dialogShell.bot().tabItem("permissions").activate());
         assertNotNull(dialogShell.bot().text("false"));
         dialogShell.bot().button("Cancel").click();
         dialogShell = null;
      } finally {
         
      }
   }
   
   /**
    * restores the initial conditions.
    */
   private void restore() {
      if(dialogShell != null) {
         dialogShell.close();
         dialogShell = null;
      }
      editor.close();
      previousperspective.activate();
      StarterPreferenceUtil.setDontAskForProofStarter(prevDontAsk);
      StarterPreferenceUtil.setSelectedProofStarterID(prevProofStarter);
      proof.dispose();
      environment.dispose();
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
      
      //Don't show the dialogs inquiring about starters and perspectives.
      previousperspective = bot.activePerspective();
      bot.perspectiveByLabel("KeY").activate();
      prevProofStarter = StarterPreferenceUtil.getSelectedProofStarterID();
      StarterPreferenceUtil.setSelectedProofStarterID("org.key_project.keyide.ui.starter.KeYIDEProofStarter");
      prevDontAsk = StarterPreferenceUtil.isDontAskForProofStarter();
      StarterPreferenceUtil.setDontAskForProofStarter(true);
      
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("LoopInvariantRuleCompletionTest");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/loopInvariantExample", src);
      
      editor = null;
      // Get local file in operating system of folder src 
      File location = ResourceUtil.getLocation(src);
      File[] filesInLoc = location.listFiles();
      assertNotNull(filesInLoc);
      assertEquals(filesInLoc.length, 1);
      File proofFolder = filesInLoc[0];
      
      
      // Load source code in KeY and get contract to proof which is the first contract of LogRecord#getBalance().
      environment = KeYEnvironment.load(new File(proofFolder, filename), null, null, null, EclipseUserInterfaceCustomization.getInstance());
      
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
   
   private void openLIDialog() {
      //click context menu / text we're looking for: The first { should be the start of the update.
      final SWTBotStyledText styledText = editor.bot().styledText();
      Point point = TestUtilsUtil.selectText(styledText, "{");
      point = new Point(point.x - 1, point.y);
      
      TestUtilsUtil.setCursorLocation(styledText, point.x, point.y);
      TestUtilsUtil.clickContextMenu(styledText, point.x, point.y, "Loop Invariant");
      SWTBotShell shell = bot.activeShell();
      
      dialogShell = shell;
      
   }
}
