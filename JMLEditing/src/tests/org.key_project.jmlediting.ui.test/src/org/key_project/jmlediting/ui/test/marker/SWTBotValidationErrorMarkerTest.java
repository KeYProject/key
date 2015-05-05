package org.key_project.jmlediting.ui.test.marker;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.keyboard.Keystrokes;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.utilities.JMLEditingUITestUtils.TestProject.SaveGuarantee;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotValidationErrorMarkerTest {

   public static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static String PROJECT_NAME = SWTBotValidationErrorMarkerTest.class.getSimpleName();
   private static String PACKAGE_NAME = SWTBotValidationErrorMarkerTest.class.getPackage().getName();
   private static String CLASS_NAME = "ValidationErrorMarkerTestClass";

   private static IProject testProject;
   private static SWTBotEclipseEditor openEditor;
   private static IFile testFile;

   @BeforeClass
   public static void initializeProjectAndOpenEditor() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
      final TestProject result = JMLEditingUITestUtils.createProjectWithFile(bot, 
                                                                   PROJECT_NAME, 
                                                                   PACKAGE_NAME, 
                                                                   CLASS_NAME,
                                                                   SaveGuarantee.SAVE_BUT_NO_CHANGES_LATER);
      testProject = result.getProject().getProject();
      JMLPreferencesHelper.setProjectJMLProfile(testProject, JMLEditingUITestUtils.findReferenceProfile());
      result.restoreClassAndOpen();
      openEditor = result.getOpenedEditor();
      testFile = result.getFile();
   }

   @Test
   public void checkErrorMarkers() throws CoreException {
      // Make a change and wait to make eclipse compile and report errors
      openEditor.typeText(0, 0, " ");
      openEditor.save();
      TestUtilsUtil.waitForBuild();
      List<Integer> errorLines = JMLEditingUITestUtils.getAllErrorLines(testFile);
      assertTrue("No error marker for line 8", errorLines.contains(8));
      assertFalse("Error marker for line 13", errorLines.contains(13));
      this.removeText(new Position(12, 4), 46);
      openEditor.save();
      TestUtilsUtil.waitForBuild();
      errorLines = JMLEditingUITestUtils.getAllErrorLines(testFile);
      assertTrue("No error marker for line 8", errorLines.contains(8));
      assertTrue("No Error marker for line 13", errorLines.contains(13));
   }

   /*
    * removes the text with given length at Position pos
    */
   private void removeText(final Position pos, final int length) {
      openEditor.selectRange(pos.line, pos.column, length);
      openEditor.pressShortcut(Keystrokes.DELETE);
   }
   
   @AfterClass
   public static void closeEditor() {
      openEditor.close();
   }
}
