package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import static org.junit.Assert.*;

import java.io.File;

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
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.test.util.TestUtilsUtil;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Proof;

public class SWTBotCompleteAndApplyTacletMatchWizardPageTest {

   private SWTWorkbenchBot bot;
   private SWTBotShell dialogShell;
   private SWTBotEditor editor;
   private SWTBotPerspective previousperspective;
   private String prevProofStarter;
   private boolean prevDontAsk;
   private Proof proof;
   private KeYEnvironment<DefaultUserInterfaceControl> environment;

   @Test
   public void initialTest() throws Exception {
      try{
         setupTest("allLeft.proof");
         openLIDialog("orall", "allLeft");
      } finally{
         restore();
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
      bot.perspectiveByLabel("KeY").activate();
      prevProofStarter = StarterPreferenceUtil.getSelectedProofStarterID();
      StarterPreferenceUtil.setSelectedProofStarterID("org.key_project.keyide.ui.starter.KeYIDEProofStarter");
      prevDontAsk = StarterPreferenceUtil.isDontAskForProofStarter();
      StarterPreferenceUtil.setDontAskForProofStarter(true);
      
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("TacletMatchWizardPageTest");
      IFolder src = project.getProject().getFolder("src");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/tacletMatchWizardExample", src);
      
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
   
   /**
    * opens a taclet Dialog.
    * @param rule The name of the rule to be applied
    */
   private void openLIDialog(String location, String rule) {
      //click context menu / text we're looking for: The first { should be the start of the update.
      final SWTBotStyledText styledText = editor.bot().styledText();
      Point point = TestUtilsUtil.selectText(styledText, location);
      point.x = point.x - 1;
      
      TestUtilsUtil.setCursorLocation(styledText, point.x, point.y);
      TestUtilsUtil.clickContextMenu(styledText, point.x, point.y, rule);
      SWTBotShell shell = bot.activeShell();
      
      dialogShell = shell;
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
}
