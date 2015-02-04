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
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.eclipse.swtbot.swt.finder.utils.TableRow;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.eclipse.swtbot.swt.finder.widgets.TimeoutException;
import org.eclipse.ui.texteditor.ITextEditor;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.test.UITestUtils.TestProject.SaveGuarantee;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class UITestUtils {

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

   public static class TestProject {

      public static enum SaveGuarantee {
         NO_SAVE, SAVE_BUT_NO_CHANGES_LATER, NO_GUARANTEE;
      }

      private final SWTWorkbenchBot bot;
      private final String projectName;
      private final String packageName;
      private final String className;
      private final String classLocation;
      private SWTBotEclipseEditor openedEditor;
      private final IJavaProject project;
      private final IFolder testFolder;
      private final SaveGuarantee saveGuarantee;

      public TestProject(final SWTWorkbenchBot bot, final String projectName,
            final String packageName, final String className,
            final String classLoc, final SaveGuarantee guarantee)
            throws CoreException, InterruptedException {
         super();
         this.bot = bot;
         this.classLocation = classLoc;
         this.projectName = projectName;
         this.project = TestUtilsUtil.createJavaProject(this.projectName);
         this.packageName = packageName;
         this.className = className;
         this.saveGuarantee = guarantee;
         // Create folders for the package
         final IFolder srcFolder = this.project.getProject().getFolder("src");
         final String[] packageFolders = this.packageName.split("\\.");
         IFolder testFolder = srcFolder;
         for (final String folder : packageFolders) {
            testFolder = TestUtilsUtil.createFolder(testFolder, folder);
         }
         this.testFolder = testFolder;
         this.openedEditor = null;
      }

      public String getClassLocation() {
         return this.classLocation;
      }

      public String getClassName() {
         return this.className;
      }

      public String getPackageName() {
         return this.packageName;
      }

      public void copyData() throws CoreException {
         // Copy the class
         BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID,
               this.classLocation, this.testFolder);
      }

      public void restoreClassAndOpen() throws CoreException {
         // Check what to do in order to restore the content of the editor to
         // the given class
         // No editor -> copy class and restore
         // No guarantee -> "
         // SAVE_BUT_NO_CHANGES_LATER && not dirty -> "

         // Otherwise try to do something faster
         if (this.openedEditor != null
               && (this.saveGuarantee == SaveGuarantee.NO_SAVE || (this.saveGuarantee == SaveGuarantee.SAVE_BUT_NO_CHANGES_LATER && this.openedEditor
                     .isDirty()))) {
            // if NO_SAVE and not dirty -> everything fine
            // else revert to saved
            if (this.saveGuarantee == SaveGuarantee.SAVE_BUT_NO_CHANGES_LATER
                  || this.openedEditor.isDirty()) {
               this.bot.getDisplay().syncExec(new Runnable() {

                  @Override
                  public void run() {
                     ((ITextEditor) TestProject.this.openedEditor
                           .getReference().getEditor(true)).doRevertToSaved();
                  }
               });
            }
         }
         else {
            if (this.openedEditor != null) {
               this.openedEditor.close();
            }
            this.copyData();
            // Open the editor
            this.bot.tree().getTreeItem(this.projectName).select().expand()
                  .getNode("src").select().expand().getNode(this.packageName)
                  .select().expand().getNode(this.className + ".java").select()
                  .doubleClick();
            this.openedEditor = this.bot.activeEditor().toTextEditor();
         }
      }

      public IJavaProject getProject() {
         return this.project;
      }

      public SWTBotEclipseEditor getOpenedEditor() {
         return this.openedEditor;
      }

   }

   /**
    * Does the same as
    * {@link UITestUtils#createProjectWithFileAndOpen(SWTWorkbenchBot, String, String, String, String)}
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
   public static TestProject createProjectWithFile(final SWTWorkbenchBot bot,
         final String projectName, final String packageName,
         final String className, final SaveGuarantee guarantee)
         throws CoreException, InterruptedException {
      return createProjectWithFile(bot, projectName, packageName, className,
            "data/template/" + className + ".java", guarantee);
   }

   public static TestProject createProjectWithFile(final SWTWorkbenchBot bot,
         final Class<?> testClass, final SaveGuarantee guarantee)
         throws CoreException, InterruptedException {
      return createProjectWithFile(bot, testClass.getSimpleName(), testClass
            .getPackage().getName(), testClass.getSimpleName(), guarantee);
   }

   /**
    * Creates a new Java Projects and copies a class into the project. The it
    * opens to class in the editor. The guarantee with respect to saving the
    * content of the opened editor influences the test speed. The higher the
    * guarantee is, the faster the test can be because the editor does not neet
    * be reopened that many times.
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
    * @param the
    *           guarantee the user of the created TestProject gives with regards
    *           to saving the content of the opened editor
    * @return an object of type {@link TestProject} which contains the editor
    *         and the project
    * @throws CoreException
    * @throws InterruptedException
    */
   public static TestProject createProjectWithFile(final SWTWorkbenchBot bot,
         final String projectName, final String packageName,
         final String className, final String classLoc,
         final SaveGuarantee guarantee) throws CoreException,
         InterruptedException {

      return new TestProject(bot, projectName, packageName, className,
            classLoc, guarantee);
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

   public static Position getLineAndColumn(final int offset,
         final SWTBotEclipseEditor editor) {
      int lineOffset = 0;
      for (int line = 0; line < editor.getLineCount(); line++) {
         int nextLineOffset = lineOffset + editor.getLines().get(line).length();
         // Check new line characters
         if (editor.getText().length() > nextLineOffset) {
            final char newLine1 = editor.getText().charAt(nextLineOffset);
            final char newLine2 = editor.getText().charAt(nextLineOffset + 1);
            if (newLine1 == '\n' && newLine2 == 'r') {
               nextLineOffset += 2;
            }
            else {
               // One new line at least
               nextLineOffset++;
            }
         }
         // Check whether offset is in line
         if (offset < nextLineOffset) {
            return new Position(line, offset - lineOffset);
         }
         lineOffset = nextLineOffset;
      }
      throw new IndexOutOfBoundsException("Offset not in text");
   }

   public static List<CommentRange> getAllJMLCommentsInEditor(
         final SWTBotEclipseEditor editor) {
      return new CommentLocator(editor.getText()).findJMLCommentRanges();

   }
}
