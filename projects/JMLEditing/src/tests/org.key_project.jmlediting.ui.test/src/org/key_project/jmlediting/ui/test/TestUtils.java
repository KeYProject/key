package org.key_project.jmlediting.ui.test;

import static org.eclipse.swtbot.swt.finder.waits.Conditions.shellCloses;
import static org.eclipse.swtbot.swt.finder.waits.Conditions.waitForMenu;
import static org.eclipse.swtbot.swt.finder.waits.Conditions.waitForShell;
import static org.junit.Assert.assertTrue;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.swt.SWTException;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.AbstractSWTBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotList;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.ui.test.preferencepages.ProfilePropertiesTest;

public class TestUtils {

   public static  IProject getProjectWithName(String name) {
      IProject[] projects = ResourcesPlugin.getWorkspace().getRoot().getProjects();
      for (IProject p : projects) {
        if ( p.getName().equals(name)) {
           return p;
        }
      }
      return null;
   }

   public static void prepareWorkbench(SWTWorkbenchBot bot) {
     // bot.resetWorkbench();
   
      try {
         // In the case that the welcome page opens, close it
         bot.viewByTitle("Welcome").close();
      } catch (WidgetNotFoundException e) {
      }
      
      bot.waitUntil(waitForMenu(bot.activeShell(),
           WidgetMatcherFactory.<MenuItem>withMnemonic("File")));
   }

   public static IProject createEmptyJavaProject(SWTWorkbenchBot bot,String name) {
      bot.menu("File").
      menu("New").
      menu("Java Project").click();
      bot.textWithLabel("&Project name:").setText(name);
      SWTBotShell activeShell = bot.activeShell();
      bot.button("Finish").click();
      bot.waitUntil(shellCloses(activeShell));
      return getProjectWithName(name);
   }

   public static  void openJMLProfileProperties(SWTWorkbenchBot bot, final String PROJECT_NAME) {
      bot.tree().getTreeItem(PROJECT_NAME).contextMenu("Properties").click(); //.select();
      
      bot.sleep(100);
   
      bot.tree().getTreeItem("JML").select();
      bot.tree().getTreeItem("JML").expand().getNode("Profile").select();
   }

   public static void validateProfileListSelection(IJMLProfile expectedProfile,
         SWTBotList profileList) {
      // Now the global default should be selected
      // Unfortunately, we only get the names of the selection from swt bot
      String[] selectedProfile = profileList.selection();
      assertTrue("Not excately one profile selected", selectedProfile.length == 1);
      assertTrue("The selected profile does not match expected one", selectedProfile[0].equals(expectedProfile.getName()));
   }

}
