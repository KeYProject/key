package org.key_project.stubby.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.stubby.core.test.testcase.StubGeneratorUtilTest;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for GenerateStubsHandler.
 * @author Martin Hentschel
 */
public class SWTBotGenerateStubsHandlerTest extends TestCase {
   /**
    * Generates stubs for the example {@code helloWorldExample}.
    */
   @Test
   public void testHelloWorldExample() throws Exception {
      // Create java project and fill it with source and expected oracle files
      IJavaProject javaProject = TestUtilsUtil.createJavaProject("SWTBotGenerateStubsHandlerTest_testHelloWorldExample");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/helloWorldExample", javaProject.getProject());
      TestUtilsUtil.waitForBuild();
      // Close welcome screen
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Set current stub folder
      assertEquals(StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH, StubGeneratorUtil.getStubFolderPath(javaProject));
      StubGeneratorUtil.setStubFolderPath(javaProject, "myStubFolder");
      // Click on project context menu to generate stubs
      SWTBotTreeItem projectItem = TestUtilsUtil.selectInProjectExplorer(bot, javaProject.getProject().getName());
      projectItem.contextMenu("Generate Stubs").click();
      // Finish wizard
      SWTBotShell shell = bot.shell("Generate Stubs");
      SWTBotText stubFolderText = shell.bot().text();
      assertEquals("myStubFolder", stubFolderText.getText());
      stubFolderText.setText("new/stub folder");
      TestUtilsUtil.clickDirectly(shell.bot().button("Finish"));
      bot.waitUntil(Conditions.shellCloses(shell));
      // Ensure that new stub folder is set
      assertEquals("new/stub folder", StubGeneratorUtil.getStubFolderPath(javaProject));
      // Extract oracle stubs into project
      IFolder oracleFolder = javaProject.getProject().getFolder("oracleStubs");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/helloWorldExample/oracleStubs", oracleFolder);
      // Compare generated stubs with oracle stubs
      IFolder stubFolder = javaProject.getProject().getFolder(new Path("new/stub folder"));
      StubGeneratorUtilTest.assertResources(oracleFolder.members(), stubFolder.members());
   }
}
