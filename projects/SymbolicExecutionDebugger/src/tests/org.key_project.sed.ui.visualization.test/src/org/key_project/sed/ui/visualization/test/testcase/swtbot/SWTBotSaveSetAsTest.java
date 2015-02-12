package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.execution_tree.wizard.SaveSetAsWizard;
import org.key_project.sed.ui.visualization.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests {@link SaveSetAsWizard}.
 * @author Martin Hentschel
 */
public class SWTBotSaveSetAsTest extends AbstractSymbolicExecutionTreeTest {
   /**
    * Launches "data/Number/test/Number.set" and saves it.
    */
   @Test
   public void testSaveAs() throws Exception {
      final PathReplacement pr = new PathReplacement("D:\\Forschung\\Development\\SymbolicExecutionDebugger\\runtime-SymbolicExecutionDebugger.product\\SED Examples\\src\\Number.java", "Number.java");
      IDiagramTestSteps testSteps = new AbstractDiagramTestSteps() {
         @Override
         public void test(SWTWorkbenchBot bot, IProject project, IFile setFile, SWTBotView debugView, SWTBotTree debugTree, ILaunch launch, ISEDDebugTarget target) throws Exception {
            // Test launch
            assertSavedFile(bot, debugTree, project, "SavedLaunchSetFile", 0);
            // Test debug target
            assertSavedFile(bot, debugTree, project, "SavedDebugTargetSetFile", 0, 0);
         }
         
         protected void assertSavedFile(SWTWorkbenchBot bot, SWTBotTree debugTree, IProject project, String fileName, int... toSelect) throws Exception {
            // Perform save
            TestSedCoreUtil.selectInDebugTree(debugTree, toSelect);
            TestUtilsUtil.clickContextMenu(debugTree, "Save Symbolic Execution Tree as Set File");
            SWTBotShell shell = bot.shell("Save as");
            shell.bot().tree().select("SWTBotSaveSetAsTest_testSaveAs");
            shell.bot().text(1).setText(fileName + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT);
            TestUtilsUtil.clickDirectly(shell.bot().button("Next >"));
            shell.bot().checkBox("Save variables").select();
            shell.bot().checkBox("Save call stack").select();
            TestUtilsUtil.clickDirectly(shell.bot().button("Finish"));
            bot.waitUntil(Conditions.shellCloses(shell));
            // Compare saved file with original one
            String expected = IOUtil.readFrom(BundleUtil.openInputStream(Activator.PLUGIN_ID, "data/Number/test/Number.set"));
            expected = applyPathReplacements(project, expected, pr);
            String current = ResourceUtil.readFrom(project.getFile(fileName + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT));
            assertEquals(expected, current);
         }
      };
      doDiagramTest("SWTBotSaveSetAsTest_testSaveAs", 
                    "data/Number/test", 
                    "Number.set", 
                    testSteps, 
                    pr);
   }
}
