package org.key_project.jmlediting.ui.test;

import static org.eclipse.swtbot.swt.finder.waits.Conditions.shellCloses;
import static org.eclipse.swtbot.swt.finder.waits.Conditions.waitForMenu;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.key_project.jmlediting.core.profile.IJMLProfile;

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
   
   public static void createEmptyPackage(SWTWorkbenchBot bot, String name) {
      bot.menu("File").menu("New").menu("Package").click();
      bot.textWithLabel("&Name:").setText(name);
      SWTBotShell activeShell = bot.activeShell();
      bot.sleep(500);
      bot.button("Finish").click();
      bot.waitUntil(shellCloses(activeShell));
   }
   
   public static void createEmptyClass(SWTWorkbenchBot bot, String packageName, String className) {
      System.out.println("--------------start createEmptyClass");
      System.out.println(bot.activeShell().getText());
      try {
         bot.activeShell().setFocus();
         bot.menu("File").setFocus();
         System.out.println(bot.menu("File"));
      bot.menu("File").menu("New").menu("Class").click();
      }catch(Exception e) {
         e.printStackTrace();
      }
      bot.sleep(2000);
//      bot.textWithLabel("&Package:").setText(packageName);
//      bot.textWithLabel("&Name:").setText(className);
//      SWTBotShell activeShell = bot.activeShell();
//      bot.sleep(2000);
//      bot.button("Finish").click();
//      bot.waitUntil(shellCloses(activeShell));
   }
   
   public static  void openJMLProfileProperties(SWTWorkbenchBot bot, final String projectName) {
      bot.tree().getTreeItem(projectName).contextMenu("Properties").click(); //.select();
      
      bot.sleep(100);
   
      bot.tree().getTreeItem("JML").select();
      bot.tree().getTreeItem("JML").expand().getNode("Profile").select();
   }

   public static void validateProfileListSelection(IJMLProfile expectedProfile,
         SWTBotTable profileList) {
      // Now the global default should be selected
      // Unfortunately, we only get the names of the selection from swt bot
      List<String> selectedProfiles = new ArrayList<String>(1);
      for (int i = 0; i < profileList.rowCount(); i++) {
         if(profileList.getTableItem(i).isChecked()) {
            selectedProfiles.add(profileList.getTableItem(i).getText());
         }
      }
      assertTrue("Not excately one profile selected", selectedProfiles.size() == 1);
      assertTrue("The selected profile does not match expected one", selectedProfiles.get(0).equals(expectedProfile.getName()));
   }

}
