package org.key_project.jmlediting.ui.test;

import static org.eclipse.swtbot.swt.finder.waits.Conditions.shellCloses;
import static org.eclipse.swtbot.swt.finder.waits.Conditions.waitForMenu;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.swtbot.swt.finder.widgets.TimeoutException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;

public class TestUtils {

   public static IProject getProjectWithName(final String name) {
      final IProject[] projects = ResourcesPlugin.getWorkspace().getRoot()
            .getProjects();
      for (final IProject p : projects) {
         if (p.getName().equals(name)) {
            return p;
         }
      }
      return null;
   }

   public static void prepareWorkbench(final SWTWorkbenchBot bot) {
      // bot.resetWorkbench();

      try {
         // In the case that the welcome page opens, close it
         bot.viewByTitle("Welcome").close();
      }
      catch (final WidgetNotFoundException e) {
      }

      bot.waitUntil(waitForMenu(bot.activeShell(),
            WidgetMatcherFactory.<MenuItem> withMnemonic("File")));
   }

   public static IProject createEmptyJavaProject(final SWTWorkbenchBot bot,
         final String name) {
      bot.menu("File").menu("New").menu("Java Project").click();
      bot.textWithLabel("&Project name:").setText(name);
      final SWTBotShell activeShell = bot.activeShell();
      bot.button("Finish").click();
      bot.waitUntil(shellCloses(activeShell));
      return getProjectWithName(name);
   }

   public static void createEmptyPackage(final SWTWorkbenchBot bot,
         final String name) {
      bot.menu("File").menu("New").menu("Package").click();
      bot.textWithLabel("&Name:").setText(name);
      final SWTBotShell activeShell = bot.activeShell();
      bot.sleep(500);
      bot.button("Finish").click();
      bot.waitUntil(shellCloses(activeShell));
   }

   public static void createEmptyClass(final SWTWorkbenchBot bot,
         final String packageName, final String className) {
      System.out.println("--------------start createEmptyClass");
      System.out.println(bot.activeShell().getText());
      try {
         bot.activeShell().setFocus();
         bot.menu("File").setFocus();
         System.out.println(bot.menu("File"));
         bot.menu("File").menu("New").menu("Class").click();
      }
      catch (final Exception e) {
         e.printStackTrace();
      }
      bot.sleep(2000);
      // bot.textWithLabel("&Package:").setText(packageName);
      // bot.textWithLabel("&Name:").setText(className);
      // SWTBotShell activeShell = bot.activeShell();
      // bot.sleep(2000);
      // bot.button("Finish").click();
      // bot.waitUntil(shellCloses(activeShell));
   }

   public static void openJMLProfileProperties(final SWTWorkbenchBot bot,
         final String projectName) {
      bot.tree().getTreeItem(projectName).contextMenu("Properties").click(); // .select();

      bot.sleep(100);

      bot.tree().getTreeItem("JML").select();
      bot.tree().getTreeItem("JML").expand().getNode("Profile").select();
   }

   public static void validateProfileListSelection(
         final IJMLProfile expectedProfile, final SWTBotTable profileList) {
      // Now the global default should be selected
      // Unfortunately, we only get the names of the selection from swt bot
      final List<String> selectedProfiles = new ArrayList<String>(1);
      for (int i = 0; i < profileList.rowCount(); i++) {
         if (profileList.getTableItem(i).isChecked()) {
            selectedProfiles.add(profileList.getTableItem(i).getText());
         }
      }
      assertTrue("Not excately one profile selected",
            selectedProfiles.size() == 1);
      assertTrue("The selected profile does not match expected one",
            selectedProfiles.get(0).equals(expectedProfile.getName()));
   }

   public static void selectFileInProject(final SWTWorkbenchBot bot,
         final String projectName, final String nodePath) {
      final String[] nodeHierachy = nodePath.split("/");
      SWTBotTreeItem item = bot.tree().getTreeItem(projectName).select()
            .expand();
      bot.sleep(1000);
      for (int i = 0; i < nodeHierachy.length - 1; i++) {
         item = item.getNode(nodeHierachy[i]).select().expand();
         bot.sleep(1000);
      }
      item.getNode(nodeHierachy[nodeHierachy.length - 1]).select()
            .doubleClick();
      bot.sleep(1000);
   }

   public static String getHoverAtPosition(final SWTWorkbenchBot bot,
         final SWTBotEclipseEditor editor, final int line, final int column) {
      editor.navigateTo(line, column);
      bot.sleep(200);
      editor.pressShortcut(KeyStroke.getInstance(SWT.F2));
      try {
         bot.waitUntil(new ShellIsActiveWithEmptyText(""));
         return bot.styledText().getText();
      }
      catch (final TimeoutException e) {
         // No hover
         return null;
      }
   }

   public static IJMLProfile findReferenceProfile() {
      for (final IJMLProfile profile : JMLProfileManagement
            .getAvailableProfiles()) {
         if (profile.getIdentifier().equals(
               "org.key_project.jmlediting.profile.jmlref")) {
            return profile;
         }
      }
      return null;
   }

}
