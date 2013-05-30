package org.key_project.key4eclipse.resources.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.junit.Test;
import org.key_project.key4eclipse.resources.ui.handlers.ConvertJavaToKeYProjectHandler;
import org.key_project.key4eclipse.resources.ui.test.util.KeY4EclipseResourcesUiTestUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link ConvertJavaToKeYProjectHandler}.
 * @author Martin Hentschel
 */
public class SWTBotConvertToKeYProjectTest extends TestCase {   
   /**
    * Creates a new {@link IJavaProject} and converts it into a KeYProject. The used view is the ProjectExplorer.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testConvertToKeYProjectInProjectExplorer() throws Exception {
      doTest("SWTBotConvertToKeYProjectTest_testConvertToKeYProjectInProjectExplorer", 
             "General", "Project Explorer");
   }
   
   /**
    * Creates a new {@link IJavaProject} and converts it into a KeYProject. The used view is the PackageExplorer.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testConvertToKeYProjectInPackageExplorer() throws Exception {
      doTest("SWTBotConvertToKeYProjectTest_testConvertToKeYProjectInPackageExplorer", 
             "Java", "Package Explorer");
   }
   
   /**
    * Creates a new {@link IJavaProject} and converts it into a KeYProject. The used view is the ProjectNavigator.
    * @throws Exception Occurred Exception.
    */
   @Test
   public void testConvertToKeYProjectInNavigator() throws Exception {
      doTest("SWTBotConvertToKeYProjectTest_testConvertToKeYProjectInNavigator", 
             "General", "Navigator");
   }
   
   /**
    * Executes the test steps.
    * @param projectName The name of the workspace project to create and to convert.
    * @param pathInOpenViewDialog The path to the view to start convertion in.
    * @throws Exception Occurred Exception.
    */
   protected void doTest(String projectName, String... pathInOpenViewDialog) throws Exception {
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
      SWTBotView view = TestUtilsUtil.openView(bot, pathInOpenViewDialog);
      TestUtilsUtil.selectInTree(view.bot().tree(), project.getProject().getName());
      TestUtilsUtil.clickContextMenu(view.bot().tree(), "Convert to KeY Project");
      TestUtilsUtil.waitForBuild();
      KeY4EclipseResourcesUiTestUtil.assertKeYNature(project.getProject());
   }
}
