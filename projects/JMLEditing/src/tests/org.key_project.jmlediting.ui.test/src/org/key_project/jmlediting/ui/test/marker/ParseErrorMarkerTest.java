package org.key_project.jmlediting.ui.test.marker;

import static org.junit.Assert.assertTrue;

import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.ui.test.TestUtils;
import org.key_project.jmlediting.ui.test.TestUtils.ProjectOpenResult;

public class ParseErrorMarkerTest {

   public static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static String PROJECT_NAME = ParseErrorMarkerTest.class
         .getSimpleName();
   private static String PACKAGE_NAME = ParseErrorMarkerTest.class.getPackage()
         .getName();
   private static String CLASS_NAME = "ParseErrorMarkerTestClass";

   private static IProject testProject;
   private static SWTBotEclipseEditor openEditor;

   @BeforeClass
   public static void initializeProjectAndOpenEditor() throws CoreException,
         InterruptedException {
      final ProjectOpenResult result = TestUtils.createProjectWithFileAndOpen(
            bot, PROJECT_NAME, PACKAGE_NAME, CLASS_NAME);
      testProject = result.project.getProject();
      openEditor = result.openedEditor;
      JMLPreferencesHelper.setProjectJMLProfile(testProject,
            TestUtils.findReferenceProfile());
   }

   @Test
   public void checkErrorMarkers() {
      openEditor.typeText(0, 0, " ");
      openEditor.save();
      bot.sleep(5000);
      final List<Integer> errorLines = TestUtils.getAllErrorLines(bot,
            CLASS_NAME + ".java");
      System.out.println(errorLines);
      assertTrue("No error marker for line 8", errorLines.contains(8));
      assertTrue("No error marker for line 10", errorLines.contains(10));
   }

}
