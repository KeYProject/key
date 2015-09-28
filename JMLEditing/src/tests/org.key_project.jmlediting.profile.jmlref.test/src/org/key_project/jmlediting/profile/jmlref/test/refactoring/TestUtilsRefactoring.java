package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import static org.junit.Assert.assertEquals;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotCheckBox;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RefactoringUtil;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Utility class for testing the move and rename refactoring with SWTBot.
 * 
 * @author Robert Heimbach
 *
 */
public class TestUtilsRefactoring {

   /**
    * Reads the content of a java file from a given folder into a String.
    * 
    * @param oracleFolder the folder the file is in.
    * @param oracleFileName the filename, can be w/ or w/o ".java" file ending.
    * @return the content of the file as a String.
    * @throws CoreException if the file could not be found.
    */
   public static String getOracle(IFolder oracleFolder, String oracleFileName)
         throws CoreException {

      IFile fileToRead;

      if (oracleFileName.endsWith(".java"))
         fileToRead = oracleFolder.getFile(oracleFileName);
      else
         fileToRead = oracleFolder.getFile(oracleFileName
               + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);

      final String oracleString = ResourceUtil.readFrom(fileToRead);

      return oracleString;
   }

   /**
    * Copies the files from copyFrom into folderToCopyInto with waiting for the build to
    * finish afterwards. Unifies line breaks when copying.
    * <p>
    * Note that the bundle ID is fixed in this implementation.
    * </p>
    * 
    * @param copyFrom the path as a string to a folder with the content to copy.
    * @param folderToCopyInto target in workspace to copy into.
    * @throws CoreException
    */
   public static void copyFiles(String copyFrom, IFolder folderToCopyInto)
         throws CoreException {

      BundleUtil.extractFromBundleToWorkspace(
            org.key_project.jmlediting.profile.jmlref.test.Activator.PLUGIN_ID, copyFrom,
            folderToCopyInto, true);

      TestUtilsUtil.waitForBuild();
   }

   /**
    * Returns the active text editor's content as a String and closes the editor afterwards.
    * 
    * @param bot SWTWorkbenchBot to access the active editor from.
    * @return the content of the active text editor as a String.
    */
   public static String getContentAfterRefactoring(SWTWorkbenchBot bot) {
      SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();

      String content = editor.getText();

      editor.close();

      return content;
   }

   /**
    * Selects the a given field in the outline view and activates the renaming process to the
    * specified new name.
    * 
    * @param fieldToChange the field to rename.
    * @param className the class the field is in (without ".java" file ending).
    * @param packageName name of the package the class is in.
    * @param srcFolder sourceFolder the specified class is in.
    * @param newName the new name to change the field's name to.
    * @param bot {@link SWTWorkbenchBot} to select the outline view from.
    * @param nameOfShell either "Rename Field" or "Rename Method" expected.
    */
   public static void selectElementInOutlineAndExecuteRenaming(String fieldToChange,
         String className, String packageName, IFolder srcFolder, String newName,
         SWTWorkbenchBot bot, String nameOfShell) {

      TestUtilsUtil.openEditor(srcFolder.getFolder(packageName).getFile(
            className + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

      // select the field in the outline view of the bot
      SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree();
      SWTBotTreeItem fieldToRename = TestUtilsUtil.selectInTree(tree, className,
            fieldToChange);

      fieldToRename.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'R');

      // Change variable name in rename dialog
      SWTBotShell renameDialog = bot.shell(nameOfShell);
      setNewElementName(newName, bot, renameDialog);
   }

   /**
    * Renames a parameter by selecting the method which uses the parameter, called methodName,
    * in the outline and then moving offset to the right in the text editor to select the
    * parameter to be renamed.
    * 
    * @param methodName the method's name which uses the parameter.
    * @param className the class the field is in (without ".java" file ending).
    * @param packageName name of the package the class is in.
    * @param srcFolder sourceFolder of the specified class.
    * @param newName the new name to change the parameter's name to.
    * @param bot {@link SWTWorkbenchBot} to select the outline view from.
    * @param offset move offset to the right to select the parameter in the text editor.
    */
   public static void selectParameterAndExecuteRenaming(String methodName, String className,
         String packageName, IFolder srcFolder, String newName, SWTWorkbenchBot bot,
         int offset) {

      TestUtilsUtil.openEditor(srcFolder.getFolder(packageName).getFile(
            className + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
      
      // select the method which uses the parameter in the outline view of the bot
      SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree();
      SWTBotTreeItem methodUsingParameter = TestUtilsUtil.selectInTree(tree, className,
            methodName);
      methodUsingParameter.click();
      methodUsingParameter.doubleClick();

      // Switch to the editor. The method is now highlighted.
      // Even though the cursor blinks behind the last character of the method's name
      // the position is instead still the beginning of the method's name.
      SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
      Position pos = editor.cursorPosition();

      // add the length of the method's name and the offset
      int newPosition = pos.column
            + methodName.substring(0, methodName.indexOf('(')).length() + offset;

      editor.navigateTo(pos.line, newPosition);

      // press the shortcut twice to enter the dialog instead of live editing
      bot.sleep(1000);
      editor.pressShortcut(SWT.ALT | SWT.SHIFT, 'R');
      bot.sleep(1000);
      editor.pressShortcut(SWT.ALT | SWT.SHIFT, 'R');

      // Change variable name in rename dialog
      SWTBotShell renameDialog = bot.shell("Rename Local Variable");
      setNewElementName(newName, bot, renameDialog);
   }

   /**
    * Selects a specified package in the package explorer and activates the renaming process
    * to a new name.
    * 
    * @param projectName the project the package to be renamed is in.
    * @param packageName the package to be renamed.
    * @param srcFolder the source folder the package is in.
    * @param newPackageName the new name of the package.
    * @param bot the {@link WorkbenchBot} to select the package in the package explorer.
    * @param activateSubpackageOption set to true if the "Rename subpackages" option should be
    *           set.
    */
   public static void selectPackageAndExecuteRenaming(String projectName, String packageName,
         IFolder srcFolder, String newPackageName, SWTWorkbenchBot bot,
         Boolean activateSubpackageOption) {

      SWTBotTreeItem packageToRename = TestUtilsUtil.selectInProjectExplorer(bot,
            projectName, "src", packageName);

      packageToRename.pressShortcut(SWT.ALT | SWT.SHIFT, 'R');

      SWTBotShell renameDialog = bot.shell("Rename Package");

      // Check if the "Rename subpackages" option if correctly set
      SWTBot renameBot = renameDialog.bot();
      SWTBotCheckBox checkBox = renameBot.checkBox("Rename subpackages");

      // activate if needed but not set || deactivate if wrongly set
      // the option remembers what was set last time (at least till the workspace closes)
      if ((activateSubpackageOption && !checkBox.isChecked())
            || (!activateSubpackageOption && checkBox.isChecked())) {
         checkBox.click();
      }

      setNewElementName(newPackageName, bot, renameDialog);
   }

   /**
    * Selects the class named className in the outline view of the SWTWorkbenchBot bot and
    * activates renaming to newClassName.
    * 
    * @param className the class to be renamed (without ".java" file ending).
    * @param packageName name of the package the class is in.
    * @param srcFolder sourceFolder of the class className.
    * @param newClassName the new name of the class.
    * @param bot {@link SWTWorkbenchBot} to select the outline view from.
    */
   public static void selectClassAndExecuteRenaming(String className, String packageName,
         IFolder srcFolder, String newClassName, SWTWorkbenchBot bot) {

      TestUtilsUtil.openEditor(srcFolder.getFolder(packageName).getFile(
            className + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

      // select the fieldToChange in the outline view of the bot
      SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree();
      SWTBotTreeItem classToRename = TestUtilsUtil.selectInTree(tree, className);

      classToRename.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'R');

      // Change variable name in rename dialog
      SWTBotShell renameDialog = bot.shell("Rename Type");
      SWTBot renameDialogBot = renameDialog.bot();
      renameDialogBot.textWithLabel("New name:").setText(newClassName);

      // start renaming and wait till finished
      renameDialogBot.button(IDialogConstants.FINISH_LABEL).click();
      bot.waitUntil(Conditions.shellCloses(renameDialog));
   }

   /**
    * Selects an element in the outline and moves it to another class.
    * 
    * @param srcFolder folder the source class is in.
    * @param fromclass class with the element which should be moved.
    * @param fromPackage package the source class is in.
    * @param destclass class to move the element to.
    * @param destpackage package the destination class is in.
    * @param elementDescription how the element to be moved appears in the outline.
    * @param bot {@link SWTWorkbenchBot} to select the outline view from.
    */
   public static void selectElementInOutlineAndMove(IFolder srcFolder, String fromclass,
         String fromPackage, String destclass, String destpackage, String elementDescription,
         SWTWorkbenchBot bot) {

      // open the class with the field to be moved in the editor
      TestUtilsUtil.openEditor(srcFolder.getFolder(fromPackage).getFile(
            fromclass + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

      // select the field in the outline and activate the renaming process
      SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree();
      SWTBotTreeItem fieldToMove = TestUtilsUtil.selectInTree(tree, fromclass,
            elementDescription);
      fieldToMove.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'V');

      SWTBotShell moveDialog = bot.shell("Move Static Members");
      SWTBot moveDialogBot = moveDialog.bot();

      // destination class needs to be given as a fully qualified name
      moveDialogBot.comboBox().setText(destpackage + "." + destclass);

      moveDialogBot.button(IDialogConstants.OK_LABEL).click();
      bot.waitUntil(Conditions.shellCloses(moveDialog));
   }

   /**
    * Selects a class in the package explorer and moves it to another package.
    * 
    * @param projectNameSrc name of the project the class to be moved is in.
    * @param className name of the class to be moved.
    * @param packageFrom package the class to be moved is in.
    * @param projectTo destination project.
    * @param packageTo destination package.
    * @param bot {@link SWTWorkbenchBot} to select the package explorer from.
    */
   public static void selectClassAndMove(String projectNameSrc, String className,
         String packageFrom, String projectTo, String packageTo, SWTWorkbenchBot bot) {

      // select the class to be moved in the package explorer
      SWTBotTree tree = TestUtilsUtil.getProjectExplorer(bot).bot().tree();
      SWTBotTreeItem classToMove = TestUtilsUtil.selectInTree(tree, projectNameSrc, "src",
            packageFrom, className + ".java");

      classToMove.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'V');

      // Change variable name in rename dialog
      SWTBotShell moveDialog = bot.shell("Move");
      SWTBot moveDialogBot = moveDialog.bot();

      // select the destination. The projects/packages/files are shown,
      // like the package explorer does, in a tree hierarchy.
      SWTBotTree moveTree = moveDialogBot.tree();
      TestUtilsUtil.selectInTree(moveTree, projectTo, "src", packageTo);

      // start renaming and wait till finished
      moveDialogBot.button(IDialogConstants.OK_LABEL).click();

      bot.waitUntil(Conditions.shellCloses(moveDialog));
   }

   /**
    * Sets the new element's name to newName in the renaming dialog.
    * 
    * @param newName the element's new name.
    * @param bot the {@link SWTWorkbenchBot} used to wait for the shell to close.
    * @param renameDialog the rename dialog / shell.
    */
   public static void setNewElementName(String newName, SWTWorkbenchBot bot,
         SWTBotShell renameDialog) {
      SWTBot renameDialogBot = renameDialog.bot();
      renameDialogBot.textWithLabel("New name:").setText(newName);

      // start renaming and wait till finished
      renameDialogBot.button(IDialogConstants.OK_LABEL).click();
      bot.waitUntil(Conditions.shellCloses(renameDialog));
   }

   /**
    * Runs a field rename test. That is, source and oracle files are copied, the field to be
    * renamed is selected in the outline and renamed. Afterwards, all files in the project are
    * compared to their oracle counterparts.
    * 
    * @param path the path of the test files with the sub folders \src and \oracle.
    * @param srcFolder the folder of the source files to load into eclipse.
    * @param oracleFolder the folder of the oracle.
    * @param bot workbench bot.
    * @param className the class the field to be renamed is in.
    * @param packageName name of the package the class is in.
    * @param outlineAppearance how the field to be renamed appears in the outline.
    * @param newName the new name to change to.
    * @param javaProject project the classes are in.
    * @throws CoreException
    */
   public static void runFieldRenameTest(String path, IFolder srcFolder,
         IFolder oracleFolder, SWTWorkbenchBot bot, String className, String packageName,
         String outlineAppearance, String newName, IJavaProject javaProject)
         throws CoreException {

      copyFiles(path + "\\src", srcFolder);
      copyFiles(path + "\\oracle", oracleFolder);

      selectElementInOutlineAndExecuteRenaming(outlineAppearance, className, packageName,
            srcFolder, newName, bot, "Rename Field");

      compareAllFilesInProjectToOracle(javaProject, oracleFolder, bot);
   }

   /**
    * Runs a method rename test. Works like the field rename test but expects a differently
    * named rename dialog.
    * 
    * @param path the path of the test files with the sub folders \src and \oracle.
    * @param srcFolder the folder of the source files to load into eclipse.
    * @param oracleFolder the folder of the oracle.
    * @param bot workbench bot.
    * @param className the class the method to be renamed is in.
    * @param packageName name of the package the class is in.
    * @param outlineAppearance how the method to be renamed appears in the outline.
    * @param newName the new name to change to.
    * @param javaProject project the classes are in.
    * @throws CoreException
    * 
    * @see {@link #runFieldRenameTest(String, IFolder, IFolder, SWTWorkbenchBot, String, String, String, String, IJavaProject)}
    */
   public static void runMethodRenameTest(String path, IFolder srcFolder,
         IFolder oracleFolder, SWTWorkbenchBot bot, String className, String packageName,
         String outlineAppearance, String newName, IJavaProject javaProject)
         throws CoreException {

      copyFiles(path + "\\src", srcFolder);
      copyFiles(path + "\\oracle", oracleFolder);

      selectElementInOutlineAndExecuteRenaming(outlineAppearance, className, packageName,
            srcFolder, newName, bot, "Rename Method");

      compareAllFilesInProjectToOracle(javaProject, oracleFolder, bot);
   }

   /**
    * Runs a class rename test. That is, source and oracle files are copied, the field to be
    * renamed is selected in the outline and renamed. Afterwards, all files in the project are
    * compared to their oracle counterparts.
    * <p>
    * Note that the oracle of the renamed class should be provided with the new name.
    * </p>
    * 
    * @param path the path of the test files with the sub folders \src and \oracle.
    * @param srcFolder the folder of the source files to load into eclipse.
    * @param oracleFolder the folder of the oracle.
    * @param bot workbench bot.
    * @param className the name of the class to be renamed.
    * @param packageName name of the package the class is in.
    * @param newClassName the new class' name.
    * @throws CoreException
    * 
    * @see {@link #runFieldRenameTest(String, IFolder, IFolder, SWTWorkbenchBot, String, String, String, String, IJavaProject)}
    * @see {@link #runMethodRenameTest(String, IFolder, IFolder, SWTWorkbenchBot, String, String, String, String, IJavaProject)}
    */
   public static void runClassRenameTestBasic(String path, IFolder srcFolder,
         IFolder oracleFolder, SWTWorkbenchBot bot, String className, String packageName,
         String newClassName, IJavaProject javaProject) throws CoreException {

      copyFiles(path + "\\src", srcFolder);
      copyFiles(path + "\\oracle", oracleFolder);

      selectClassAndExecuteRenaming(className, packageName, srcFolder, newClassName, bot);

      compareAllFilesInProjectToOracle(javaProject, oracleFolder, bot);
   }

   /**
    * Runs a parameter rename test. That is, source and oracle files are copied, the method
    * with the parameter to be renamed is selected in the outline and with the help of an
    * offset the parameter is selected in the editor and renamed. Afterwards, all files in the
    * project are compared to their oracle counterparts.
    * 
    * @param path the path of the test files with the sub folders \src and \oracle.
    * @param srcFolder the folder of the source files to load into eclipse.
    * @param oracleFolder the folder of the oracle.
    * @param bot workbench bot.
    * @param className the class the parameter to be renamed is in.
    * @param packageName name of the package the class with the parameter is in.
    * @param methodName how the method which uses the parameter to be renamed appears in the
    *           outline.
    * @param newName the parameter's new name.
    * @param offset how much in the text editor to move to the right to select the parameter
    *           when the method with the name methodName is selected.
    * @throws CoreException
    * 
    * @see {@link #selectParameterAndExecuteRenaming(String, String, String, IFolder, String, SWTWorkbenchBot, int)}
    */
   public static void runParameterRenameTest(String path, IFolder srcFolder,
         IFolder oracleFolder, SWTWorkbenchBot bot, String className, String packageName,
         String methodName, String newName, int offset) throws CoreException {

      copyFiles(path + "\\src", srcFolder);
      copyFiles(path + "\\oracle", oracleFolder);

      selectParameterAndExecuteRenaming(methodName, className, packageName, srcFolder,
            newName, bot, offset);

      assertEquals(getOracle(oracleFolder, className), getContentAfterRefactoring(bot));
   }

   /**
    * Runs a package rename test. First, source and oracle files are copied, then the package
    * is selected in the package explorer and after the renaming all files in the project are
    * compared to their oracle counterparts.
    * 
    * @param path the path of the test files with the sub folders \src and \oracle.
    * @param srcFolder the folder of the source files to load into eclipse.
    * @param oracleFolder the folder of the oracle.
    * @param bot workbench bot.
    * @param packageName name of the package to be renamed.
    * @param newPackageName the new name of the package.
    * @param project the {@link IJavaProject} containing the package to be renamed.
    * @param renameSubpackages true if the "Rename subpackages" option should be set.
    * @throws CoreException
    */
   public static void runPackageRenameTest(String path, IFolder srcFolder,
         IFolder oracleFolder, SWTWorkbenchBot bot, String packageName,
         String newPackageName, IJavaProject project, Boolean renameSubpackages)
         throws CoreException {

      copyFiles(path + "\\src", srcFolder);
      copyFiles(path + "\\oracle", oracleFolder);

      selectPackageAndExecuteRenaming(project.getElementName(), packageName, srcFolder,
            newPackageName, bot, renameSubpackages);

      compareAllFilesInProjectToOracle(project, oracleFolder, bot);
   }

   /**
    * Runs a field or method move test. First, source and oracle files are copied, then the
    * element to be moved is selected in the outline and after the moving the file named
    * "Main" in the package "mainpack" is compared to its oracle.
    * 
    * @param path the path of the test files with the sub folders \src and \oracle.
    * @param srcFolder the folder of the source files to load into eclipse.
    * @param oracleFolder the folder of the oracle.
    * @param bot workbench bot.
    * @param classNameMoveFrom the class the element to be moved is in.
    * @param packageName name of the package the class is in.
    * @param elementDescription how the element to be moved appears in the outline.
    * @param classNameMoveTo destination class.
    * @param javaProject project the classes are in.
    * @throws CoreException
    */
   public static void runMoveOutlineElementTest(String path, IFolder srcFolder,
         IFolder oracleFolder, SWTWorkbenchBot bot, String classNameMoveFrom,
         String packageName, String elementDescription, String classNameMoveTo,
         String packageTo, IJavaProject javaProject) throws CoreException {

      copyFiles(path + "\\src", srcFolder);
      copyFiles(path + "\\oracle", oracleFolder);

      selectElementInOutlineAndMove(srcFolder, classNameMoveFrom, packageName,
            classNameMoveTo, packageTo, elementDescription, bot);

      TestUtilsUtil.openEditor(srcFolder.getFolder("mainpack").getFile(
            "Main" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

      // Movements of the JDT will result in added tabs in front of the moved method or field
      assertEquals(getOracle(oracleFolder, "Main"),
            getContentAfterRefactoring(bot).replace("\t", "    "));
   }

   /**
    * Runs a move class test. A class is selected in the package explorer and moved. Note that
    * only the class with the name "Main" in the package "mainpack" is compared to its oracle.
    * 
    * @param path the path of the test files with the sub folders \src and \oracle.
    * @param srcFolder the folder of the source files to load into eclipse.
    * @param oracleFolder the folder of the oracle.
    * @param bot workbench bot.
    * @param classNameMoveFrom name of the class to be moved.
    * @param packageFrom name of the package the class is in.
    * @param packageTo destination package.
    * @param javaProject project the classes are in.
    * @throws CoreException
    */
   public static void runMoveClassTest(String path, IFolder srcFolder, IFolder oracleFolder,
         SWTWorkbenchBot bot, String classNameMoveFrom, String packageFrom, String packageTo,
         IJavaProject javaProject) throws CoreException {

      copyFiles(path + "\\src", srcFolder);
      copyFiles(path + "\\oracle", oracleFolder);

      String projectName = javaProject.getElementName();

      selectClassAndMove(projectName, classNameMoveFrom, packageFrom, projectName, packageTo,
            bot);

      compareFileToOracle(srcFolder, oracleFolder, "mainpack", "Main", bot);
   }

   /**
    * Compares one given class to its oracle.
    * 
    * @param srcFolder the folder the class to be compared is in.
    * @param oracleFolder the folder the oracle is in.
    * @param packageName the package the class is in.
    * @param classNameToCompare the name of the class to be compared.
    * @param bot a workbench bot.
    * @throws CoreException
    */
   public static void compareFileToOracle(IFolder srcFolder, IFolder oracleFolder,
         String packageName, String classNameToCompare, SWTWorkbenchBot bot)
         throws CoreException {

      TestUtilsUtil.openEditor(srcFolder.getFolder(packageName).getFile(
            classNameToCompare + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

      assertEquals(getOracle(oracleFolder, classNameToCompare),
            getContentAfterRefactoring(bot));
   }

   /**
    * Compares all files of a given project to the files in a given folder of oracle files.
    * 
    * @param project project which files should be compared.
    * @param oracleFolder folder which contains the oracle files.
    * @param bot {@link SWTWorkbenchBot} to make the actions.
    * @throws CoreException thrown if the packages of the project could not be accessed.
    */
   public static void compareAllFilesInProjectToOracle(IJavaProject project,
         IFolder oracleFolder, SWTWorkbenchBot bot) throws CoreException {
      for (IPackageFragment fragment : RefactoringUtil
            .getAllPackageFragmentsContainingSources(project)) {
         for (ICompilationUnit unit : fragment.getCompilationUnits()) {
            assertEquals(getOracle(oracleFolder, unit.getElementName()), unit.getSource());
         }
      }
   }

   /**
    * Adds the projects which names are provided in the String array {@code referencedProjects}
    * to the java build path of another specified project with the name {@code projectToAddTo}.
    * 
    * @param projectToAddTo project which build path needs additional entries.
    * @param referencedProjects other projects to add to the build path of projectToAddTo.
    * @param bot {@link SWTWorkbenchBot} to make the required UI actions.
    */
   public static void setProjectReferences(String projectToAddTo,
         String[] referencedProjects, SWTWorkbenchBot bot) {

      SWTBotTreeItem projectToAddReferences = TestUtilsUtil.selectInProjectExplorer(bot,
            projectToAddTo);
      projectToAddReferences.select().pressShortcut(SWT.ALT, SWT.CR);

      // select the build path "Java Build Path" and "Projects" tab
      SWTBotShell propertiesDialog = bot.shell("Properties for " + projectToAddTo);
      TestUtilsUtil.selectInTree(propertiesDialog.bot().tree(), "Java Build Path").click();

      SWTBot propertiesDialogBot = propertiesDialog.bot();
      propertiesDialogBot.tabItem("Projects").activate();
      propertiesDialogBot.button("Add...").click();

      SWTBotShell projectSelection = bot.shell("Required Project Selection");
      SWTBot projectSelectionBot = projectSelection.bot();

      // select the projects to add in the shown table
      SWTBotTable table = projectSelectionBot.table(0);
      for (String projectToAdd : referencedProjects) {
         table.doubleClick(table.indexOf(projectToAdd), 0);
         table.pressShortcut(0, SWT.SPACE);
      }

      // finish the process.
      projectSelectionBot.button(IDialogConstants.OK_LABEL).click();
      propertiesDialogBot.waitUntil(Conditions.shellCloses(projectSelection));

      propertiesDialogBot.button(IDialogConstants.OK_LABEL).click();
      bot.waitUntil(Conditions.shellCloses(propertiesDialog));
   }

   /**
    * Creates a project, sets the JML profile to the default JML profile and creates a folder
    * called "oracle".
    * 
    * @param projectName name of the project to create.
    * @return the created {@link IProject}.
    * @throws CoreException thrown if the project could not be created.
    * @throws InterruptedException thrown if the creation of the project is interrupted.
    */
   public static IProject setupProjectAndOracle(String projectName) throws CoreException,
         InterruptedException {
      final IJavaProject javaProject = TestUtilsUtil.createJavaProject(projectName);
      final IProject project = javaProject.getProject();
      TestUtilsUtil.createFolder(project, "oracle");
      JMLPreferencesHelper.setProjectJMLProfile(project,
            JMLPreferencesHelper.getDefaultJMLProfile());
      return project;
   }

   /**
    * Creates a project with a folder called "oracle" and copies the needed files for testing
    * into the "src" and "oracle" folder of the project.
    * 
    * @param projectName name of the project to create.
    * @param path path of the file system where the files to copy are. Expects a "src" and
    *           "oracle" folder.
    * @return the created {@link IProject}.
    * @throws CoreException thrown when the project could not be created.
    * @throws InterruptedException thrown if the project creation was interrupted.
    */
   public static IProject createProjectWithFiles(String projectName, String path)
         throws CoreException, InterruptedException {
      final IProject project = setupProjectAndOracle(projectName);

      String pathToTests = path + "\\src";
      String pathToOracle = path + "\\oracle";

      TestUtilsRefactoring.copyFiles(pathToTests,
            project.getFolder(JDTUtil.getSourceFolderName()));
      TestUtilsRefactoring.copyFiles(pathToOracle, project.getFolder("oracle"));

      return project;
   }

   /**
    * Deletes all packages (and subpackages) and thus also all files from a given folder.
    * 
    * @param folder given {@link IFolder} to delete the files from.
    * @throws CoreException thrown if the packages could not be accessed.
    */
   public static void deleteAllPackagesFromFolder(IFolder folder) throws CoreException {
      for (IResource member : folder.members()) {
         if (member instanceof IFolder && member.exists()) {
            folder.getFolder(member.getName()).delete(false, null);
         }
      }
   }
}