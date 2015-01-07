package org.key_project.jmlediting.ui.test;

import static org.eclipse.swtbot.swt.finder.waits.Conditions.shellCloses;
import static org.eclipse.swtbot.swt.finder.waits.Conditions.waitForMenu;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.matchers.WidgetMatcherFactory;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.utils.TableRow;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.swtbot.swt.finder.widgets.TimeoutException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

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

   public static class ProjectOpenResult {
      public final SWTBotEclipseEditor openedEditor;
      public final IJavaProject project;

      public ProjectOpenResult(final SWTBotEclipseEditor openFile,
            final IJavaProject project) {
         super();
         this.openedEditor = openFile;
         this.project = project;
      }

   }

   /**
    * Does the same as
    * {@link TestUtils#createProjectWithFileAndOpen(SWTWorkbenchBot, String, String, String, String)}
    * but implies the location of the class file. The source file to copy should
    * be located in data/template/CLASSNAME.java
    * 
    * @param bot
    *           the bot to use
    * @param projectName
    *           the project name
    * @param packageName
    *           the package name
    * @param className
    *           the class name
    * @return the project and opened editor
    * @throws CoreException
    * @throws InterruptedException
    */
   public static ProjectOpenResult createProjectWithFileAndOpen(
         final SWTWorkbenchBot bot, final String projectName,
         final String packageName, final String className)
         throws CoreException, InterruptedException {
      return createProjectWithFileAndOpen(bot, projectName, packageName,
            className, "data/template/" + className + ".java");
   }

   /**
    * Creates a new Java Projects and copies a class into the project. The it
    * opens to class in the editor.
    *
    * @param bot
    *           the bot to use
    * @param projectName
    *           the name for the new project
    * @param packageName
    *           the package name of the class (with dots)
    * @param className
    *           the class name
    * @param classLoc
    *           the location where the class source file is located and from
    *           which it should be copied
    * @return an object of type {@link ProjectOpenResult} which contains the
    *         editor and the project
    * @throws CoreException
    * @throws InterruptedException
    */
   public static ProjectOpenResult createProjectWithFileAndOpen(
         final SWTWorkbenchBot bot, final String projectName,
         final String packageName, final String className, final String classLoc)
         throws CoreException, InterruptedException {

      final IJavaProject project = TestUtilsUtil.createJavaProject(projectName);
      // Create folders for the package
      final IFolder srcFolder = project.getProject().getFolder("src");
      final String[] packageFolders = packageName.split("\\.");
      IFolder testFolder = srcFolder;
      for (final String folder : packageFolders) {
         testFolder = TestUtilsUtil.createFolder(testFolder, folder);
      }
      // Copy the class
      BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, classLoc,
            testFolder);
      // Open the editor
      bot.tree().getTreeItem(projectName).select().expand().getNode("src")
            .select().expand().getNode(packageName).select().expand()
            .getNode(className + ".java").select().doubleClick();
      return new ProjectOpenResult(bot.activeEditor().toTextEditor(), project);
   }

   /**
    * Searches for all error markers which are visibile in the problems view.
    *
    * @param bot
    *           the bot to use
    * @return all tree items in the problems view, which belong to an error
    */
   public static SWTBotTreeItem[] getAllErrorItems(final SWTWorkbenchBot bot) {

      // Search the view
      SWTBotView problemsView = null;
      for (final SWTBotView view : bot.views()) {
         if ("Problems".equals(view.getTitle())) {
            problemsView = view;
         }
      }
      if (problemsView == null) {
         // Could try to open view by menu
         // But it is open in our product
         return new SWTBotTreeItem[0];
      }
      // Navigate to the Errors item
      final SWTBotTree problemTree = problemsView.bot().tree();
      SWTBotTreeItem errorItem = null;
      for (final SWTBotTreeItem item : problemTree.getAllItems()) {
         if (item.getText().startsWith("Errors")) {
            errorItem = item;
            break;
         }
      }
      if (errorItem == null) {
         return new SWTBotTreeItem[0];
      }
      errorItem.expand();

      return errorItem.getItems();
   }

   /**
    * Returns all line number, for which an error marker is available and which
    * belongs to the given file.
    *
    * @param bot
    *           the bot to use
    * @param file
    *           the file name, not its path
    * @return a list of all line numbers, may contain duplicates if there are
    *         multiple markers for a line
    */
   public static List<Integer> getAllErrorLines(final SWTWorkbenchBot bot,
         final String file) {
      final List<Integer> lines = new ArrayList<Integer>();
      final SWTBotTreeItem[] errorItems = getAllErrorItems(bot);
      for (final SWTBotTreeItem item : errorItems) {
         final TableRow row = item.row();
         final String line = row.get(3);
         final String resource = row.get(1);
         // Remove the "line " prefix and convert to int
         final int lineNumber = Integer.parseInt(line.substring(5));
         if (file.equals(resource)) {
            lines.add(lineNumber);
         }
      }
      return lines;
   }
}
