package org.key_project.stubby.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.stubby.core.test.testcase.StubGeneratorUtilTest;
import org.key_project.stubby.ui.test.Activator;
import org.key_project.stubby.ui.test.uti.StubbyUITestUtil;
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
      //StubbyUITestUtil.closeWelcomeView();
      // Click on project context menu to generate stubs
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      SWTBotTreeItem projectItem = StubbyUITestUtil.selectInProjectExplorer(bot, javaProject.getProject().getName());
      projectItem.contextMenu("Generate Stubs").click();
      // Extract oracle stubs into project
      IFolder oracleFolder = javaProject.getProject().getFolder("oracleStubs");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/helloWorldExample/oracleStubs", oracleFolder);
      // Compare generated stubs with oracle stubs
      IFolder stubFolder = javaProject.getProject().getFolder("stubs");
      StubGeneratorUtilTest.assertResources(oracleFolder.members(), stubFolder.members());
   }
}
