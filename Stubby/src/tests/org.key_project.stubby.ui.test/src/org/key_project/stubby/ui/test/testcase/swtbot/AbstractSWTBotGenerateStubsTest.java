package org.key_project.stubby.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;
import org.osgi.framework.Bundle;

/**
 * Provides basic functionality to test stub generation.
 * @author Martin Hentschel
 */
public abstract class AbstractSWTBotGenerateStubsTest extends TestCase {
   /**
    * Performs a stub generation test.
    * @param projectName The name of the project to perform test in.
    * @param bundleId The {@link Bundle} ID of the {@link Bundle} which contains the source files.
    * @param pathToSourceFiles The path in the {@link Bundle} to the source files.
    * @param steps The {@link IGeneratorTestSteps} to perform.
    * @throws Exception Occurred Exception.
    */
   protected void doGenerationTest(String projectName,
                                   String bundleId,
                                   String pathToSourceFiles,
                                   IGeneratorTestSteps steps) throws Exception {
      // Create java project and fill it with source and expected oracle files
      IJavaProject javaProject = TestUtilsUtil.createJavaProject(projectName);
      if (pathToSourceFiles != null) {
         BundleUtil.extractFromBundleToWorkspace(bundleId, pathToSourceFiles, javaProject.getProject().getFolder(JDTUtil.getSourceFolderName()));
      }
      TestUtilsUtil.waitForBuild();
      // Close welcome screen
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Set current stub folder
      assertNotNull(steps);
      steps.initProject(javaProject);
      // Click on project context menu to generate stubs
      SWTBotTreeItem projectItem = TestUtilsUtil.selectInProjectExplorer(bot, javaProject.getProject().getName());
      projectItem.contextMenu("Generate Stubs").click();
      // Finish wizard
      SWTBotShell shell = bot.shell("Generate Stubs");
      SWTBotText stubFolderText = shell.bot().text();
      steps.testAndSetSettings(shell, stubFolderText);
      TestUtilsUtil.clickDirectly(shell.bot().button("Finish"));
      steps.wizardFinished(shell);
      bot.waitUntil(Conditions.shellCloses(shell));
      // Ensure that new stub folder is set
      steps.testResults(javaProject);
   }
   
   /**
    * Steps performed by {@link AbstractSWTBotGenerateStubsTest#doGenerationTest(String, String, String, IGeneratorTestSteps)}.
    * @author Martin Hentschel
    */
   protected static interface IGeneratorTestSteps {
      /**
       * Initializes the created {@link IJavaProject}.
       * @param javaProject The {@link IJavaProject} to initialize.
       * @throws Exception Occurred Exception.
       */
      public void initProject(IJavaProject javaProject) throws Exception;

      /**
       * Tests the dialog content and may sets settings.
       * @param shell The {@link SWTBotShell} of the {@link Wizard}.
       * @param stubFolderText The {@link SWTBotText} defining the stub folder
       * @throws Exception Occurred Exception.
       */
      public void testAndSetSettings(SWTBotShell shell, SWTBotText stubFolderText) throws Exception;
      
      /**
       * Called after the {@link Wizard} has finished.
       * @param shell The {@link SWTBotShell} of the {@link Wizard}.
       */
      public void wizardFinished(SWTBotShell shell);
      
      /**
       * Tests the generation results.
       * @param javaProject The {@link IJavaProject} to test.
       * @throws Exception Occurred Exception.
       */
      public void testResults(IJavaProject javaProject) throws Exception;
   }
}
