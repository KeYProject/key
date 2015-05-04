package org.key_project.stubby.ui.test.testcase.swtbot;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.swt.finder.utils.SWTBotPreferences;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotText;
import org.junit.Test;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@code GenerateStubsHandler}.
 * @author Martin Hentschel
 */
public class SWTBotGenerateStubsHandlerTest extends AbstractSWTBotGenerateStubsTest {
   /**
    * Generates stubs for the example {@code helloWorldExample}.
    */
   @Test
   public void testHelloWorldExample() throws Exception {
      doGenerationTest("SWTBotGenerateStubsHandlerTest_testHelloWorldExample", 
                       Activator.PLUGIN_ID, 
                       "data/helloWorldExample/src",
                       new IGeneratorTestSteps() {
                          @Override
                          public void initProject(IJavaProject javaProject) throws Exception {
                             assertEquals(StubGeneratorUtil.DEFAULT_STUB_FOLDER_PATH, StubGeneratorUtil.getStubFolderPath(javaProject));
                             StubGeneratorUtil.setStubFolderPath(javaProject, "myStubFolder");
                             
                          }
                          
                          @Override
                          public void testAndSetSettings(SWTBotShell shell, SWTBotText stubFolderText) throws Exception {
                             assertEquals("myStubFolder", stubFolderText.getText());
                             stubFolderText.setText("new/stub folder");
                             // Ensure that not part of KeY
                             long originalTimeout = SWTBotPreferences.TIMEOUT;
                             try {
                                SWTBotPreferences.TIMEOUT = 500;
                                shell.bot().radio("Not considered").click();
                             }
                             catch (Exception e) {
                                // Nothing to do
                             }
                             finally {
                                SWTBotPreferences.TIMEOUT = originalTimeout;
                             }
                          }

                          @Override
                          public void wizardFinished(SWTBotShell shell) {
                          }

                          @Override
                          public void testResults(IJavaProject javaProject) throws Exception {
                             assertEquals("new/stub folder", StubGeneratorUtil.getStubFolderPath(javaProject));
                             // Extract oracle stubs into project
                             IFolder oracleFolder = javaProject.getProject().getFolder("oracleStubs");
                             BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/helloWorldExample/oracleStubs", oracleFolder);
                             // Compare generated stubs with oracle stubs
                             IFolder stubFolder = javaProject.getProject().getFolder(new Path("new/stub folder"));
                             TestUtilsUtil.assertResources(oracleFolder.members(), stubFolder.members());
                          }
                       });
   }
}
