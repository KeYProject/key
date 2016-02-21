package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import static org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory.widgetOfType;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotPerspective;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotStyledText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTableItem;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
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
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;

/**
 * Tests for CompleteAndApplyTacletMatchWizardPage.
 * @author Viktor Pfanschilling
 *
 */
public class SWTBotCompleteAndApplyTacletMatchWizardPageTest {
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

   @Test
   public void testFinish() throws Exception {
      try {
         //load a proof file:
         setupTest("allLeft.proof");
         openRuleDialog("ellForm", "local_cut");
         
         //edit the table
         SWTBotTable t = dialogShell.bot().table();
         SWTBotTableItem ti = t.getTableItem(2);
         ti.click();

         Text wdgt = bot.widget(widgetOfType(Text.class), t.widget);
         SWTBotText txt = new SWTBotText(wdgt, null);
         txt.setText("1!=3");
         txt.pressShortcut(KeyStroke.getInstance(SWT.CR));
         
         //finish the dialog
         dialogShell.bot().button("Finish").click();
         final SWTBotStyledText styledText = editor.bot().styledText();
         //assert that the expected change happened.
         assertTrue(styledText.getText().contains("!1 = 3"));
         
         //TODO: im Proof (Goal) überprüfen, siehe andere Tests
         //load() ersetzen in allen Tests
      } finally {
         restore();
      }
   }
   
   @Test
   public void testCancel() throws Exception {
      try {
         //load a proof file
         setupTest("allLeft.proof");
         openRuleDialog("ellForm", "local_cut");
         
         String oldEditorText = editor.bot().styledText().getText();
         
         //edit the spec to unlock the finish button.
         SWTBotTable t = dialogShell.bot().table();
         SWTBotTableItem ti = t.getTableItem(2);
         ti.click();
         Text wdgt = bot.widget(widgetOfType(Text.class), t.widget);
         SWTBotText txt = new SWTBotText(wdgt, null);
         txt.setText("1!=3");
         txt.pressShortcut(KeyStroke.getInstance(SWT.CR));
         //cancel
         dialogShell.bot().button("Cancel").click();
         
         //assert that nothing has changed.
         final SWTBotStyledText styledText = editor.bot().styledText();
         assertFalse(styledText.getText().contains("!1 = 3"));

         String newEditorText = editor.bot().styledText().getText();
         assertTrue(oldEditorText.equals(newEditorText));
         
      } finally {
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
      environment = KeYEnvironment.load(
            SymbolicExecutionJavaProfile.getDefaultInstance(false), 
            new File(proofFolder, filename),
            null, null, null, SymbolicExecutionTreeBuilder.createPoPropertiesToForce(),
            EclipseUserInterfaceCustomization.getInstance(), true);
      
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
    * opens a Taclet Dialog.
    * @param location The text snippet where to look for the rule
    * @param rule The name of the rule to be applied
    */
   private void openRuleDialog(String location, String rule) {
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
