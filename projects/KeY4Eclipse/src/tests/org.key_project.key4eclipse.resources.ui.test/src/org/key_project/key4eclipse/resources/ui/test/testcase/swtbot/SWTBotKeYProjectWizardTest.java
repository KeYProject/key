package org.key_project.key4eclipse.resources.ui.test.testcase.swtbot;

import junit.framework.TestCase;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.junit.Test;
import org.key_project.key4eclipse.resources.ui.test.util.KeY4EclipseResourcesTestUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Tests for {@link KeYProjectWizard}. 
 * @author Stefan Käsdorf
 */
public class SWTBotKeYProjectWizardTest extends TestCase{
   
   private SWTWorkbenchBot bot;
   
   @Test
   public void testKeYProjectWizard() throws CoreException, InterruptedException{
      bot = new SWTWorkbenchBot();

      TestUtilsUtil.closeWelcomeView(bot);
      createKeYProject(bot, "KeYProjectWizardTest");
      TestUtilsUtil.waitForBuild();
      
      IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();

      IProject project = root.getProject("KeYProjectWizardTest");
      KeY4EclipseResourcesTestUtil.assertKeYNature(project);
   }
   
   public static void createKeYProject(SWTWorkbenchBot bot, String name){
      bot.menu("File").menu("New").menu("Project...").click();
      
      SWTBotShell shell = bot.shell("New Project");
      shell.activate();
      bot.tree().expandNode("KeY").select("KeY Project");
      bot.button("Next >").click();
 
      bot.textWithLabel("Project name:").setText(name);
 
      bot.button("Finish").click();
}
   
}
