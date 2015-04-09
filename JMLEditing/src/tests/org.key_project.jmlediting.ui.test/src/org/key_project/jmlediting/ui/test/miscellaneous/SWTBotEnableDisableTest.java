package org.key_project.jmlediting.ui.test.miscellaneous;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper.ColorProperty;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotEnableDisableTest {

   public static SWTWorkbenchBot bot = new SWTWorkbenchBot();
   private final RGB javaCommentRGB = new RGB(63, 127, 95);
   private static String PROJECT_NAME = SWTBotEnableDisableTest.class.getSimpleName();
   private static String PACKAGE_NAME = SWTBotEnableDisableTest.class.getPackage().getName();
   private static String CLASS_NAME = "EnableDisableTestClass";

   private static IProject testProject;
   private static SWTBotEclipseEditor openEditor;
   private static IFile testFile;
   private Set<RGB> jmlColors = null;

   @BeforeClass
   public static void initializeProjectAndOpenEditor() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
      final TestProject result = JMLEditingUITestUtils.createProjectWithFile(bot, PROJECT_NAME, PACKAGE_NAME, CLASS_NAME, SaveGuarantee.SAVE_BUT_NO_CHANGES_LATER);
      testProject = result.getProject().getProject();
      JMLPreferencesHelper.setProjectJMLProfile(testProject, JMLEditingUITestUtils.findReferenceProfile());
      result.restoreClassAndOpen();
      openEditor = result.getOpenedEditor();
      testFile = result.getFile();
   }

   @Test
   public void testBasics() throws CoreException {
      this.jmlColors = new HashSet<RGB>(Arrays.asList(JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.COMMENT), 
                                                      JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.KEYWORD),
                                                      JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.TOPLEVEL_KEYWORD)));
      // Open the JML properties page for the project
      SWTBotShell preferenceShell = JMLEditingUITestUtils.openJMLPreferencePage(bot);

      SWTBotCheckBox enableDisableJMLFeature = preferenceShell.bot().checkBox("Enable JML Integration");

      // Now we are in a profile properties page
      // Because this project is null, we require that there are no project
      // specific settings
      assertTrue("JML Feature was disabled at start",enableDisableJMLFeature.isChecked());

      preferenceShell.bot().button(IDialogConstants.CANCEL_LABEL).click();

      List<Integer> errorLines = JMLEditingUITestUtils.getAllErrorLines(testFile);
      assertTrue("Error lines are: " + CollectionUtil.toString(errorLines), errorLines.contains(8));
      assertTrue("Error lines are: " + CollectionUtil.toString(errorLines), errorLines.contains(11));
      this.checkColors(6, 5, 10, this.jmlColors, "Colors did not match JMLColors.");

      preferenceShell = JMLEditingUITestUtils.openJMLPreferencePage(bot);

      enableDisableJMLFeature = preferenceShell.bot().checkBox("Enable JML Integration");
      // Disable JML Features
      enableDisableJMLFeature.deselect();

      // Apply the properties
      preferenceShell.bot().button("Apply").click();

      // Want to do the rebuild
      SWTBotShell confirmationShell = preferenceShell.bot().shell("JML Editing Turned On or Off");
      confirmationShell.bot().button(IDialogConstants.YES_LABEL).click();

      // Rebuild should be done by now.
      errorLines = JMLEditingUITestUtils.getAllErrorLines(testFile);
      assertFalse(errorLines.contains(8));
      assertFalse(errorLines.contains(11));
      this.checkColors(6, 5, 10, this.javaCommentRGB, "Color did not match JavaCommentColor");
   }

   private void checkColors(final int line, final int column, final int length, final Set<RGB> colors, final String message) {
      final StyleRange[] textColors = openEditor.getStyles(line, column, length);
      for (final StyleRange r : textColors) {
         assertTrue(message + " at " + r.start + " with length " + r.length, colors.contains(r.foreground.getRGB()));
      }
   }

   private void checkColors(final int line, final int column, final int length, final RGB color, final String message) {
      this.checkColors(line, column, length, Collections.singleton(color), message);
   }
   
   @AfterClass
   public static void closeEditor() {
      openEditor.close();
   }
}
