/**
 * 
 */
package org.key_project.sed.key.ui.test.testcase.swtbot;

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.waits.Conditions;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.junit.Test;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.test.util.DebugTargetResumeSuspendListener;
import org.key_project.sed.core.test.util.TestSedCoreUtil;
import org.key_project.sed.key.core.test.testcase.swtbot.AbstractKeYDebugTargetTestCase;
import org.key_project.sed.key.ui.test.Activator;
import org.key_project.sed.key.ui.view.ManualView;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.view.ExecutionTreeView;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class SWTBotSymbolicExecutionTreePruneTest extends AbstractKeYDebugTargetTestCase {
	
	@Test
	public void testPruning() throws Exception {

		IKeYDebugTargetTestExecutor executor = new IKeYDebugTargetTestExecutor() {

			@Override
			public void test(final SWTWorkbenchBot bot, IJavaProject project, IMethod method, String targetName, SWTBotView debugView, SWTBotTree debugTree, final ISEDebugTarget target, ILaunch launch) throws Exception {
				// resume on thread
				TestUtilsUtil.closeView(ExecutionTreeView.VIEW_ID);
				SWTBotTreeItem item = TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0);
				resume(bot, item, target);

				// Wait until diagram is completely constructed
				TestUtilsUtil.openView(ExecutionTreeView.VIEW_ID);
				TestUtilsUtil.waitForJobs();

				// path to the test files
				String pathToOracleFiles = "data/number/oracle";
				
				// test diagram before prune
				assertDiagram(bot, project.getProject(), "Number.set", "data/number/oracle", null);
				
				SWTBotView manualView = bot.viewById(ManualView.VIEW_ID);
				SWTBotTree tree = manualView.bot().tree();
				
				// prune branch node
				TestUtilsUtil.selectInTree(tree, "Null Reference (n = null)");
				TestUtilsUtil.clickContextMenu(tree, "Prune Proof");
				TestSedCoreUtil.waitForDebugTreeInterface();
				TestUtilsUtil.sleep(10000); // TODO need a better solution
				// test diagram after prune
				assertDiagram(bot, project.getProject(), "NumberBranchNode.set", pathToOracleFiles, null);
				
				// prune node
				TestUtilsUtil.selectInTree(tree, "10:if (this.content==n.content) {                         return  true; }                 else  {                         return  false; }");
				TestUtilsUtil.clickContextMenu(tree, "Prune Proof");
				TestSedCoreUtil.waitForDebugTreeInterface();
				TestUtilsUtil.sleep(10000); // TODO need a better solution
				// test diagram after prune
				assertDiagram(bot, project.getProject(), "NumberNode.set", pathToOracleFiles, null);
				
				// resume on thread
				final SWTBotTreeItem item2 = TestSedCoreUtil.selectInDebugTree(debugView, 0, 0, 0);
				DebugTargetResumeSuspendListener.run(bot, target, true, new Runnable() {
					@Override
					public void run() {
						resume(bot, item2, target);
					}
				});
				TestUtilsUtil.sleep(10000); // TODO need a better solution
				// test diagram after resume
				assertDiagram(bot, project.getProject(), "NumberResume.set", pathToOracleFiles, null);
				
			}

			@Override
			public void configureDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
				TestUtilsUtil.openView(ManualView.VIEW_ID);
			}

			@Override
			public void cleanupDebugPerspective(SWTWorkbenchBot bot, IPerspectiveDescriptor debugPerspective) throws Exception {
				if (TestUtilsUtil.findView(ManualView.VIEW_ID) != null) {
					TestUtilsUtil.closeView(ManualView.VIEW_ID);
				}
			}
		};

		doKeYDebugTargetTest("SWTBotSymbolicExecutionTreePruneTest_testPruning", Activator.PLUGIN_ID, "data/number/test", false, false, createMethodSelector("Number", "equals", "QNumber;"), null, null, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.FALSE, Boolean.TRUE, 8, executor);
	}

	public static void assertDiagram(SWTWorkbenchBot bot, IProject project, String pathToSetFile, String pathToOracleFiles, String fileNameSuffix) throws Exception {
		// Open Save diagram wizard
		SWTBotView executionTreeView = bot.viewById(ExecutionTreeView.VIEW_ID);
		executionTreeView.setFocus();
		TestUtilsUtil.getToolbarButtonWithId(executionTreeView, "saveAs").click();
		// Finish wizard
		SWTBotShell wizardShell = bot.shell("Save Symbolic Execution Tree Diagram");
		wizardShell.bot().tree().select(project.getName());
		final String fileName = "Current" + IOUtil.getFileNameWithoutExtension(pathToSetFile) + (fileNameSuffix != null ? fileNameSuffix : "");
		wizardShell.bot().text(1).setText(fileName);
		TestUtilsUtil.clickDirectly(wizardShell.bot().button("Next >"));
		TestUtilsUtil.clickDirectly(wizardShell.bot().button("Finish"));
		bot.waitUntil(Conditions.shellCloses(wizardShell));
		// set true to generate new test files in the oracle dir which is defined by pathToOracleFiles
		if (false) {
			// Save oracle files
			File targetOracleDirectory = new File(pathToOracleFiles);
			ResourceUtil.copyIntoFileSystem(project.getFile(fileName + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT), new File(targetOracleDirectory, fileName + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION_WITH_DOT));
			ResourceUtil.copyIntoFileSystem(project.getFile(fileName + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT), new File(targetOracleDirectory, fileName + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT));
		} else {
			// Read diagram files
			String expectedDiagramFile = IOUtil.readFrom(BundleUtil.openInputStream(Activator.PLUGIN_ID, pathToOracleFiles + "/" + fileName + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT));
			String currentDiagramFile = ResourceUtil.readFrom(project.getFile(fileName + ExecutionTreeUtil.DIAGRAM_FILE_EXTENSION_WITH_DOT));

			// delete IDs in both files because they differ
			expectedDiagramFile = expectedDiagramFile.replaceAll("value=\"_[a-zA-Z0-9\\-]*", "#######");
			currentDiagramFile = currentDiagramFile.replaceAll("value=\"_[a-zA-Z0-9\\-]*", "#######");
			
			// Compare diagram files
			if (!StringUtil.equalIgnoreWhiteSpace(expectedDiagramFile, currentDiagramFile)) {
				// Let test fail to have an improved comparison dialog
				assertEquals(expectedDiagramFile, currentDiagramFile); 
			}
		}
	}
}
