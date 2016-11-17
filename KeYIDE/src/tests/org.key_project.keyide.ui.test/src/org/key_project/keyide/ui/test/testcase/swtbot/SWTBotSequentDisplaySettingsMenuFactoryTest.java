package org.key_project.keyide.ui.test.testcase.swtbot;

import java.io.File;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEditor;
import org.eclipse.ui.IEditorPart;
import org.junit.Test;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.editor.SequentDisplaySettingsMenuFactory;
import org.key_project.swtbot.swing.bot.SwingBotJEditorPane;
import org.key_project.swtbot.swing.bot.SwingBotJFrame;
import org.key_project.ui.test.util.TestKeYUIUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.TestUtilsUtil.ResultWithException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.gui.actions.HidePackagePrefixToggleAction;
import de.uka.ilkd.key.gui.actions.PrettyPrintToggleAction;
import de.uka.ilkd.key.gui.actions.TermLabelMenu;
import de.uka.ilkd.key.gui.actions.UnicodeToggleAction;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.UnicodeHelper;

/**
 * <p>
 * SWTBot tests for {@link SequentDisplaySettingsMenuFactory}.
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
public class SWTBotSequentDisplaySettingsMenuFactoryTest extends AbstractSWTBotKeYEditorTest {
   /**
    * Tests the hiding of a single term label.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testTermLabelHiding() throws Exception {
      ISequentViewTestSteps steps = new ISequentViewTestSteps() {
         @Override
         public void test(IJavaProject project, KeYEnvironment<?> environment, Proof proof, SWTWorkbenchBot bot, SWTBotEditor editor, KeYEditor keyEditor, SWTBotEclipseEditor textEditor, SwingBotJFrame keyMainFrame) {
            // Test initial Sequent
            assertSequent(textEditor, keyMainFrame, "==> (myPackage.MyClass.value >= 0)<<undef, selectSK>>");
            // Disable displaying of term labels in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(TermLabelMenu.TERM_LABEL_MENU).menu("selectSK").click();
            assertSequent(textEditor, keyMainFrame, "==> (myPackage.MyClass.value >= 0)<<undef>>");
            // Enable displaying of term labels in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(TermLabelMenu.TERM_LABEL_MENU).menu("selectSK").click();
            assertSequent(textEditor, keyMainFrame, "==> (myPackage.MyClass.value >= 0)<<undef, selectSK>>");
            // Disable displaying of term labels in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").menu(TermLabelMenu.TERM_LABEL_MENU).item("selectSK").clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> (myPackage.MyClass.value >= 0)<<undef>>");
            // Enable displaying of term labels in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").menu(TermLabelMenu.TERM_LABEL_MENU).item("selectSK").clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> (myPackage.MyClass.value >= 0)<<undef, selectSK>>");
         }
      };
      doLabeledSequentTest("SWTBotSequentDisplaySettingsMenuFactoryTest_testTermLabelHiding", steps);
   }
   
   /**
    * Tests the display term labels settings.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testDisplayTermLabels() throws Exception {
      ISequentViewTestSteps steps = new ISequentViewTestSteps() {
         @Override
         public void test(IJavaProject project, KeYEnvironment<?> environment, Proof proof, SWTWorkbenchBot bot, SWTBotEditor editor, KeYEditor keyEditor, SWTBotEclipseEditor textEditor, SwingBotJFrame keyMainFrame) {
            // Test initial Sequent
            assertSequent(textEditor, keyMainFrame, "==> (myPackage.MyClass.value >= 0)<<undef, selectSK>>");
            // Disable displaying of term labels in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(TermLabelMenu.TERM_LABEL_MENU).menu(TermLabelMenu.DisplayLabelsCheckBox.LABEL).click();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
            // Enable displaying of term labels in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(TermLabelMenu.TERM_LABEL_MENU).menu(TermLabelMenu.DisplayLabelsCheckBox.LABEL).click();
            assertSequent(textEditor, keyMainFrame, "==> (myPackage.MyClass.value >= 0)<<undef, selectSK>>");
            // Disable displaying of term labels in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").menu(TermLabelMenu.TERM_LABEL_MENU).item(TermLabelMenu.DisplayLabelsCheckBox.LABEL).clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
            // Enable displaying of term labels in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").menu(TermLabelMenu.TERM_LABEL_MENU).item(TermLabelMenu.DisplayLabelsCheckBox.LABEL).clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> (myPackage.MyClass.value >= 0)<<undef, selectSK>>");
         }
      };
      doLabeledSequentTest("SWTBotSequentDisplaySettingsMenuFactoryTest_testDisplayTermLabels", steps);
   }
   
   /**
    * Performs a sequent view settings test.
    * @param projectName The name of the Eclpse project to create.
    * @param sequentSteps The {@link ISequentViewTestSteps} to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doLabeledSequentTest(final String projectName, 
                                       final ISequentViewTestSteps sequentSteps) throws Exception {
      boolean originalPrettySyntax = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
      boolean originalUnicode = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUseUnicode();
      boolean originalPackage = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isHidePackagePrefix();
      try {
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(true);
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUseUnicode(false);
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHidePackagePrefix(false);
         IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
            @Override
            public void test(IJavaProject project,
                             KeYEnvironment<DefaultUserInterfaceControl> environment, 
                             Proof proof, 
                             SWTWorkbenchBot bot, 
                             SWTBotEditor editor,
                             KeYEditor keyEditor) throws Exception {
               final Shell shell = keyEditor.getSite().getShell();
               // Instantiate a proof also in KeY's MainWindow
               final File keyFile = proof.getEnv().getJavaModel().getInitialFile();
               final KeYEnvironment<WindowUserInterfaceControl> uiEnvironment = WindowUserInterfaceControl.loadInMainWindow(keyFile, null, null, null, true);
               try {
                  SwingBotJFrame keyMainFrame = TestKeYUIUtil.keyGetMainWindow();
                  // Close editor, it is not needed because it shows a different proof
                  editor.close();
                  // Open same proof in the KeYIDE
                  ResultWithException<Void> run = new ResultWithException<Void>() {
                     @Override
                     public Void doRun() throws Exception {
                        StarterUtil.openProofStarter(shell, uiEnvironment.getLoadedProof(), uiEnvironment, null, false, false, false, false);
                        return null;
                     }
                  };
                  ResultWithException.syncExec(run);
                  editor = bot.activeEditor();
                  SWTBotEclipseEditor textEditor = editor.toTextEditor();
                  IEditorPart editorPart = editor.getReference().getEditor(true); 
                  assertTrue(editorPart instanceof KeYEditor);
                  sequentSteps.test(project, uiEnvironment, uiEnvironment.getLoadedProof(), bot, editor, (KeYEditor) editorPart, textEditor, keyMainFrame);
               }
               finally {
                  uiEnvironment.dispose();
                  TestKeYUIUtil.keyCloseMainWindow();
               }
            }
         };
         doEditorTest(projectName, 
                      "data/sequentDisplaySettings", 
                      false, 
                      "MyLabeledProblem.key", 
                      false, 
                      steps);
      }
      finally {
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(originalPrettySyntax);
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUseUnicode(originalUnicode);
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHidePackagePrefix(originalPackage);
      }
   }
   
   /**
    * Tests the package hiding settings.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testPackageHiding() throws Exception {
      ISequentViewTestSteps steps = new ISequentViewTestSteps() {
         @Override
         public void test(IJavaProject project, KeYEnvironment<?> environment, Proof proof, SWTWorkbenchBot bot, SWTBotEditor editor, KeYEditor keyEditor, SWTBotEclipseEditor textEditor, SwingBotJFrame keyMainFrame) {
            // Test initial Sequent
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
            // Enable package hiding in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(HidePackagePrefixToggleAction.NAME).click();
            assertSequent(textEditor, keyMainFrame, "==> MyClass.value >= 0");
            // Disable package hiding in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(HidePackagePrefixToggleAction.NAME).click();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
            // Enable package hiding in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").item(HidePackagePrefixToggleAction.NAME).clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> MyClass.value >= 0");                  
            // Disable package hiding in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").item(HidePackagePrefixToggleAction.NAME).clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
         }
      };
      doSequentTest("SWTBotSequentDisplaySettingsMenuFactoryTest_testPackageHiding", steps);
   }
   
   /**
    * Tests the unicode settings.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testUnicode() throws Exception {
      ISequentViewTestSteps steps = new ISequentViewTestSteps() {
         @Override
         public void test(IJavaProject project, KeYEnvironment<?> environment, Proof proof, SWTWorkbenchBot bot, SWTBotEditor editor, KeYEditor keyEditor, SWTBotEclipseEditor textEditor, SwingBotJFrame keyMainFrame) {
            // Test initial Sequent
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
            // Enable unicode in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(UnicodeToggleAction.NAME).click();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value " + UnicodeHelper.GEQ + " 0");
            // Disable unicode in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(UnicodeToggleAction.NAME).click();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
            // Enable unicode in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").item(UnicodeToggleAction.NAME).clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value " + UnicodeHelper.GEQ + " 0");                  
            // Disable unicode in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").item(UnicodeToggleAction.NAME).clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
         }
      };
      doSequentTest("SWTBotSequentDisplaySettingsMenuFactoryTest_testUnicode", steps);
   }
   
   /**
    * Tests the pretty syntax settings.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testPrettySyntax() throws Exception {
      ISequentViewTestSteps steps = new ISequentViewTestSteps() {
         @Override
         public void test(IJavaProject project, KeYEnvironment<?> environment, Proof proof, SWTWorkbenchBot bot, SWTBotEditor editor, KeYEditor keyEditor, SWTBotEclipseEditor textEditor, SwingBotJFrame keyMainFrame) {
            // Test initial Sequent
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
            // Disable pretty syntax in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(PrettyPrintToggleAction.NAME).click();
            assertSequent(textEditor, keyMainFrame, "==> geq(int::select(heap, null, myPackage.MyClass::$value), Z(0(#)))");
            // Enable pretty syntax in Eclipse
            textEditor.contextMenu(SequentDisplaySettingsMenuFactory.MENU_NAME).menu(PrettyPrintToggleAction.NAME).click();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");
            // Disable pretty syntax in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").item(PrettyPrintToggleAction.NAME).clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> geq(int::select(heap, null, myPackage.MyClass::$value), Z(0(#)))");
            // Enable pretty syntax in KeY'S Main Window
            keyMainFrame.bot().jMenuBar().menu("View").item(PrettyPrintToggleAction.NAME).clickAndWait();
            assertSequent(textEditor, keyMainFrame, "==> myPackage.MyClass.value >= 0");                  
         }
      };
      doSequentTest("SWTBotSequentDisplaySettingsMenuFactoryTest_testPrettySyntax", steps);
   }
   
   /**
    * Performs a sequent view settings test.
    * @param projectName The name of the Eclpse project to create.
    * @param sequentSteps The {@link ISequentViewTestSteps} to execute.
    * @throws Exception Occurred Exception.
    */
   protected void doSequentTest(final String projectName, 
                                final ISequentViewTestSteps sequentSteps) throws Exception {
      boolean originalPrettySyntax = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
      boolean originalUnicode = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUseUnicode();
      boolean originalPackage = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isHidePackagePrefix();
      try {
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(true);
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUseUnicode(false);
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHidePackagePrefix(false);
         IKeYEditorTestSteps steps = new IKeYEditorTestSteps() {
            @Override
            public void test(IJavaProject project,
                             KeYEnvironment<DefaultUserInterfaceControl> environment, 
                             Proof proof, 
                             SWTWorkbenchBot bot, 
                             SWTBotEditor editor,
                             KeYEditor keyEditor) throws Exception {
               // Instantiate a proof also in KeY's MainWindow
               File keyFile = proof.getEnv().getJavaModel().getInitialFile();
               KeYEnvironment<WindowUserInterfaceControl> uiEnvironment = WindowUserInterfaceControl.loadInMainWindow(keyFile, null, null, null, true);
               try {
                  SwingBotJFrame keyMainFrame = TestKeYUIUtil.keyGetMainWindow();
                  SWTBotEclipseEditor textEditor = editor.toTextEditor();
                  sequentSteps.test(project, environment, proof, bot, editor, keyEditor, textEditor, keyMainFrame);
               }
               finally {
                  uiEnvironment.dispose();
                  TestKeYUIUtil.keyCloseMainWindow();
               }
            }
         };
         doEditorTest(projectName, 
                      "data/sequentDisplaySettings", 
                      false, 
                      "MyProblem.key", 
                      false, 
                      steps);
      }
      finally {
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(originalPrettySyntax);
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUseUnicode(originalUnicode);
         ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHidePackagePrefix(originalPackage);
      }
   }
   
   /**
    * Test steps to execute by {@link SWTBotSequentDisplaySettingsMenuFactoryTest#doSequentTest(ISequentViewTestSteps)}.
    * @author Martin Hentschel
    */
   protected interface ISequentViewTestSteps {
      /**
       * Performs the test steps.
       */
      public void test(IJavaProject project,
                       KeYEnvironment<?> environment, 
                       Proof proof, 
                       SWTWorkbenchBot bot, 
                       SWTBotEditor editor,
                       KeYEditor keyEditor,
                       SWTBotEclipseEditor textEditor,
                       SwingBotJFrame keyMainFrame);
   }
   
   /**
    * Ensures that the sequent is shown in both, the Eclipse editor and in KeY's Main Window.
    * @param textEditor The Eclipse Editor.
    * @param keyMainFrame KeY's Main Window.
    * @param expectedSequent The expected sequent.
    */
   protected void assertSequent(SWTBotEclipseEditor textEditor, SwingBotJFrame keyMainFrame, String expectedSequent) {
      // Test Eclipse Editor of the KeYIDEs
      String text = textEditor.getText();
      if (!StringUtil.equalIgnoreWhiteSpace(text, expectedSequent + "  Node Nr 0")) {
         assertEquals(expectedSequent + "  Node Nr 0", text);
      }
      // Test KeY's Main Window
      SwingBotJEditorPane sequentPane = keyMainFrame.bot().jEditorPane();
      String sequentText = StringUtil.trim(sequentPane.getText());
      sequentText = sequentText.replace((char) 160, ' ');
      if (!StringUtil.equalIgnoreWhiteSpace(sequentText.trim(), expectedSequent.trim())) {
         assertEquals(expectedSequent.trim(), sequentText.trim());
      }
   }
}
