package org.key_project.jmlediting.ui.test.marker;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.keyboard.Keystrokes;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.UITestUtils;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject.SaveGuarantee;

public class ValidationErrorMarkerTest {

   public static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static String PROJECT_NAME = ValidationErrorMarkerTest.class
         .getSimpleName();
   private static String PACKAGE_NAME = ValidationErrorMarkerTest.class
         .getPackage().getName();
   private static String CLASS_NAME = "ValidationErrorMarkerTestClass";

   private static IProject testProject;
   private static SWTBotEclipseEditor openEditor;

   /*
    * removes the text with given length at Position pos
    */
   private void removeText(final Position pos, final int length) {
      openEditor.selectRange(pos.line, pos.column, length);
      bot.sleep(100);
      openEditor.pressShortcut(Keystrokes.DELETE);
   }

   @BeforeClass
   public static void initializeProjectAndOpenEditor() throws CoreException,
   InterruptedException {
      final TestProject result = UITestUtils.createProjectWithFile(bot,
            PROJECT_NAME, PACKAGE_NAME, CLASS_NAME,
            SaveGuarantee.SAVE_BUT_NO_CHANGES_LATER);
      testProject = result.getProject().getProject();
      JMLPreferencesHelper.setProjectJMLProfile(testProject,
            UITestUtils.findReferenceProfile());
      result.restoreClassAndOpen();
      openEditor = result.getOpenedEditor();
   }

   @Test
   public void checkErrorMarkers() {
      // Make a change and wait to make eclipse compile and report errors
      openEditor.typeText(0, 0, " ");
      openEditor.save();
      bot.sleep(5000);
      List<Integer> errorLines = UITestUtils.getAllErrorLines(bot, CLASS_NAME
            + ".java");
      assertTrue("No error marker for line 8", errorLines.contains(8));
      assertFalse("Error marker for line 13", errorLines.contains(13));
      this.removeText(new Position(12, 4), 46);
      openEditor.save();
      bot.sleep(5000);
      errorLines = UITestUtils.getAllErrorLines(bot, CLASS_NAME + ".java");
      assertTrue("No Error marker for line 13", errorLines.contains(13));
   }

}
