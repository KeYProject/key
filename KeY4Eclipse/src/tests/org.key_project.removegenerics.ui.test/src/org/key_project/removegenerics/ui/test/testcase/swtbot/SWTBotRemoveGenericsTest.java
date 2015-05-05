package org.key_project.removegenerics.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IFolder;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.Test;
import org.key_project.removegenerics.ui.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests the removing of generics.
 * @author Martin Hentschel
 */
public class SWTBotRemoveGenericsTest extends TestCase {
   /**
    * Tests removing of generics
    * @throws Exception Occurred Exception
    */
   @Test
   public void testRemoveGenerics() throws Exception {
      // Create project
      IJavaProject project = TestUtilsUtil.createJavaProject("SWTBotRemoveGenericsTest_testRemoveGenerics");
      IFolder src = project.getProject().getFolder(JDTUtil.getSourceFolderName());
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/removeGenericsExample/src", src);
      TestUtilsUtil.waitForBuild();
      // Close welcome view
      SWTWorkbenchBot bot = new SWTWorkbenchBot();
      TestUtilsUtil.closeWelcomeView(bot);
      // Open remove generics wizard
      SWTBotTreeItem item = TestUtilsUtil.selectInProjectExplorer(bot, project.getProject().getName());
      item.contextMenu("Remove Generics").click();
      SWTBotShell wizardShell = bot.shell("Remove Generics");
      TestUtilsUtil.clickDirectly(wizardShell.bot().button(IDialogConstants.FINISH_LABEL));
      // Create oracle folder
      IFolder oracle = TestUtilsUtil.createFolder(project.getProject(), "oracle");
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, "data/removeGenericsExample/oracle", oracle);
      // Test modified content
      TestUtilsUtil.assertResources(oracle.members(), src.members());
   }
}
