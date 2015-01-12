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
import org.key_project.jmlediting.ui.test.UITestUtils;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject;

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
      final TestProject result = UITestUtils.createProjectWithFile(bot,
            PROJECT_NAME, PACKAGE_NAME, CLASS_NAME);
      result.reloadClassAndOpen();
      testProject = result.getProject().getProject();
      openEditor = result.getOpenedEditor();
      JMLPreferencesHelper.setProjectJMLProfile(testProject,
            UITestUtils.findReferenceProfile());
   }

   @Test
   public void checkErrorMarkers() {
      // Make a change and wait to make eclipse compile and report errors
      openEditor.typeText(0, 0, " ");
      openEditor.save();
      bot.sleep(5000);
      final List<Integer> errorLines = UITestUtils.getAllErrorLines(bot,
            CLASS_NAME + ".java");
      System.out.println(errorLines);
      assertTrue("No error marker for line 8", errorLines.contains(8));
      assertTrue("No error marker for line 10", errorLines.contains(10));
   }

}
