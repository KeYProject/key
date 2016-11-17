package org.key_project.key4eclipse.common.ui.test.testcase.swtbot;

import static org.eclipse.swtbot.swt.finder.matchers.WidgetMatcherFactory.widgetOfType;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
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
import org.key_project.keyide.ui.perspectives.KeYPerspective;
import org.key_project.keyide.ui.starter.KeYIDEProofStarter;
import org.key_project.util.collection.ImmutableList;
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
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;

/**
 * Tests for CompleteAndApplyTacletMatchWizardPage.
 * @author Viktor Pfanschilling
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
   
   /**
    * Indicates whether the taclet filter was originally enabled or not.
    */
   private boolean originalTacletFilter;

   /**
    * Tests whether finishing the dialog works as expected.
    * @throws Exception
    */
   @Test
   public void testFinish() throws Exception {
      try {
         //load a proof file:
         setupTest("allLeft.proof");
         openRuleDialog("ellForm", "local_cut", 0);
         
         //edit the table
         SWTBotTable t = dialogShell.bot().table();
         SWTBotTableItem ti = t.getTableItem(1);
         ti.click();

         Text wdgt = bot.widget(widgetOfType(Text.class), t.widget);
         SWTBotText txt = new SWTBotText(wdgt, null);
         txt.setText("1!=3");
         
         //finish the dialog
         dialogShell.bot().button("Finish").click();
         //assert that the expected change happened.
         assertTrue(proof.openGoals().head().toString().contains("!1 = 3"));
      } finally {
         restore();
      }
   }
   
   /**
    * Tests whether cancelling the dialog works as expected.
    * @throws Exception
    */
   @Test
   public void testCancel() throws Exception {
      try {
         //load a proof file
         setupTest("allLeft.proof");
         openRuleDialog("ellForm", "local_cut", 0);
         
         String oldEditorText = proof.openGoals().head().toString();
         
         //edit the spec to unlock the finish button.
         SWTBotTable t = dialogShell.bot().table();
         SWTBotTableItem ti = t.getTableItem(1);
         ti.click();
         Text wdgt = bot.widget(widgetOfType(Text.class), t.widget);
         SWTBotText txt = new SWTBotText(wdgt, null);
         txt.setText("1!=3");
         
         //cancel
         dialogShell.bot().button("Cancel").click();
         
         //assert that nothing has changed.
         assertFalse(proof.openGoals().head().toString().contains("!1 = 3"));

         String newEditorText = proof.openGoals().head().toString();
         assertTrue(oldEditorText.equals(newEditorText));
         
      } finally {
         restore();
      }
   }
   
   /**
    * Tests whether picking pre-set assumptions works as expected.
    * @throws Exception
    */
   @Test
   public void testAssumptions() throws Exception {
      try {
         //load a proof file
         setupTest("multiSelectsInAssume.proof");
         openRuleDialog("y", "multiSelectsInAssume", 2);

         //backup the old open goal's text
         String oldProofText = proof.openGoals().head().toString();
         
         //instantiate the two assumptions
         dialogShell.bot().comboBox("").setSelection("5 >= 0");
         dialogShell.bot().comboBox("").setSelection("10 >= 0");
         dialogShell.bot().button("Finish").click();
         
         //assert that expected change happened
         String newProofText = proof.openGoals().head().toString();
         assertFalse(oldProofText.contains("true"));
         assertTrue(newProofText.contains("true"));
         assertFalse(oldProofText.equals(newProofText));
      } finally {
         restore();
      }
   }
   
   /**
    * Tests whether manually defining assumptions works as expected.
    * @throws Exception
    */
   @Test
   public void testAssumptionsManualInput() throws Exception {
      try {
         //load a proof file
         setupTest("multiSelectsInAssume.proof");
         openRuleDialog("y", "multiSelectsInAssume", 2);
         
         //backup the old open goal's text
         String oldProofText = proof.openGoals().head().toString();
         
         //instantiate the two assumptions
         dialogShell.bot().comboBox("").setText("6 >= 0");
         dialogShell.bot().comboBox("").setText("7 >= 0");
         dialogShell.bot().button("Finish").click();
         
         //assert that expected change happened:
         //Namely, that we have two goals, one with the assumption true, one where we try to prove the assumption.
         ImmutableList<Goal> goals = proof.openGoals();
         Goal goal2 = goals.head();
         Goal goal1 = goals.tail().head();
         String g1Text = goal1.toString();
         String g2Text = goal2.toString();
         assertFalse(oldProofText.contains("true"));
         assertTrue(g1Text.contains("6 >= 0 & 7 >= 0, x * y >= 0"));
         assertTrue(g2Text.contains("7 >= 0, 6 >= 0"));
         assertTrue(g2Text.contains("true"));
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
      bot.perspectiveById(KeYPerspective.PERSPECTIVE_ID).activate();
      prevProofStarter = StarterPreferenceUtil.getSelectedProofStarterID();
      StarterPreferenceUtil.setSelectedProofStarterID(KeYIDEProofStarter.STARTER_ID);
      prevDontAsk = StarterPreferenceUtil.isDontAskForProofStarter();
      StarterPreferenceUtil.setDontAskForProofStarter(true);
      
      // Create test project
      IJavaProject project = TestUtilsUtil.createJavaProject("TacletMatchWizardPageTest");
      IFolder src = project.getProject().getFolder(JDTUtil.getSourceFolderName());
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/tacletMatchWizardExample/proofs", src);
      
      editor = null;
      // Get local file in operating system of folder src 
      File location = ResourceUtil.getLocation(src);
      
      // Load proof file in KeY
      environment = KeYEnvironment.load(
            SymbolicExecutionJavaProfile.getDefaultInstance(false), 
            new File(location, filename),
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
      
      originalTacletFilter = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().tacletFilter();
      //Deactivate taclet filter, so that we can use the required Taclets.
      ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setTacletFilter(false);
      
      editor = bot.activeEditor();
      assertNotNull(editor);
   }
   
   /**
    * opens a Taclet Dialog.
    * @param location The text snippet where to look for the rule
    * @param rule The name of the rule to be applied
    * @param offset The offset in chars where to click relative to location
    */
   private void openRuleDialog(String location, String rule, int offset) {
      //click context menu / text we're looking for.
      final SWTBotStyledText styledText = editor.bot().styledText();
      Point point = TestUtilsUtil.selectText(styledText, location);
      point.x = point.x - 1 + offset;
      
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
      //restore Interactions
      ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().setTacletFilter(originalTacletFilter);
      
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
