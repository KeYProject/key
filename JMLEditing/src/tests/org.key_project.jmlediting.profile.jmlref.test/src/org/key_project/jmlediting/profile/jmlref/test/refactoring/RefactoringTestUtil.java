package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import static org.junit.Assert.assertEquals;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotEclipseEditor;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.utils.Position;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.profile.jmlref.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * Utility class for testing refactoring with SWTBot.
 * 
 * @author Robert Heimbach
 *
 */
public class RefactoringTestUtil {

    /**
     * Reads the content of a java file from a given folder into a String.
     * 
     * @param oracleFolder the folder the file is in.
     * @param oracleFileName the filename, can be w/ or w/o .java file ending.
     * @return the content of the file as a String.
     * @throws CoreException if the file could not be found.
     */
    public static String getOracle(IFolder oracleFolder, String oracleFileName) throws CoreException {
        
        IFile fileToRead;
        
        if (oracleFileName.endsWith(".java"))
            fileToRead = oracleFolder.getFile(oracleFileName); 
        else
            fileToRead = oracleFolder.getFile(oracleFileName + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT);
    
        final String oracleString = ResourceUtil.readFrom(fileToRead);  // can throw CoreException
        
        return oracleString;
    }
    
    
    /**
     * Copies the files from copyFrom into folderToCopyInto with waiting for the build to finish afterwards.
     * 
     * @param copyFrom the path as a string to a folder in a bundle with the content to copy.
     * @param folderToCopyInto target in workspace to copy into.
     * @throws CoreException
     */
    public static void copyFiles(String copyFrom, IFolder folderToCopyInto) throws CoreException{
        
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, copyFrom, folderToCopyInto);
        
        TestUtilsUtil.waitForBuild(); 
    }
    

    /**
     * Returns the active text editor's content as a String and replaces
     * any \n with \r\n because oracle files were created with windows.
     * 
     * @param bot SWTWorkbenchBot to access the active editor from.
     * @return the content of the active text editor as a String.
     */
    public static String getContentAfterRefactoring(SWTWorkbenchBot bot){
        SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
        
        String content = editor.getText();
        
        editor.close();
        
        return content.replaceAll("(\n)", "\r\n");
    }
    
    
    /**
     * Selects the field fieldToChange of the class className in the outline view of the SWTWorkbenchBot bot and
     * activates renaming to newName.
     * 
     * @param fieldToChange the field to rename.
     * @param className the class the field is in (without .java file ending).
     * @param packageName name of the package the class is in.
     * @param srcFolder sourceFolder of the class className.
     * @param newName the new name to change the field's name to.
     * @param bot SWTWorkbenchBot to select the outline view from.
     */
    public static void selectFieldAndExecuteRenaming(String fieldToChange, String className, String packageName, IFolder srcFolder, String newName, SWTWorkbenchBot bot){
        
        TestUtilsUtil.openEditor(srcFolder.getFolder(packageName).getFile(className + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // select the fieldToChange in the outline view of the bot
        SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree(); 
        SWTBotTreeItem fieldToRename = TestUtilsUtil.selectInTree(tree, className, fieldToChange);
        
        fieldToRename.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'R');
                
        // Change variable name in rename dialog
        SWTBotShell renameDialog = bot.shell("Rename Field");      
        setNewElementName(newName, bot, renameDialog);
    }
    
    /**
     * Renames a parameter by selecting the method which uses the parameter, called methodName,
     * in the outline and then moving offset to the right in the text editor to select the parameter to be renamed. 
     * 
     * @param methodName the method's name which uses the parameter.
     * @param className the class the field is in (without .java file ending).
     * @param packageName name of the package the class is in.
     * @param srcFolder sourceFolder of the class className.
     * @param newName the new name to change the local variable's name to.
     * @param bot SWTWorkbenchBot to select the outline view from.
     * @param offset move offset to the right to select the parameter in the text editor.
     */
    public static void selectParameterAndExecuteRenaming(String methodName, String className, String packageName, IFolder srcFolder, String newName, SWTWorkbenchBot bot, int offset){
        
        TestUtilsUtil.openEditor(srcFolder.getFolder(packageName).getFile(className + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // select the method which uses the local variable in the outline view of the bot
        SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree(); 
        SWTBotTreeItem methodUsingLocalVar = TestUtilsUtil.selectInTree(tree, className, methodName);
        methodUsingLocalVar.click();
        methodUsingLocalVar.doubleClick();
        
        // Switch to the editor, the method should be highlighted and the cursor behind the last character
        SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
        Position pos = editor.cursorPosition();
        
        int newPosition = pos.column + methodName.substring(0, methodName.indexOf('(')).length() + offset;
        
        editor.navigateTo(pos.line, newPosition);
        
        editor.pressShortcut(SWT.ALT | SWT.SHIFT, 'R');
        editor.pressShortcut(SWT.ALT | SWT.SHIFT, 'R');
                
        // Change variable name in rename dialog
        SWTBotShell renameDialog = bot.shell("Rename Local Variable");      
        setNewElementName(newName, bot, renameDialog);
    }


    /**
     * Sets the new element's name to newName in the renaming dialog.
     * @param newName the element's new name.
     * @param bot the workbench bot, used to wait for the shell to close.
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
     * Runs a basic field rename test. That is, only one project, one file and renaming of one field.
     * 
     * @param path the path of the test files with the sub folders \src and \oracle. 
     * @param srcFolder the folder of the source files to load into eclipse.
     * @param oracleFolder the folder of the oracle.
     * @param bot workbench bot.
     * @param className the class the field to be renamed is in.
     * @param packageName name of the package the class is in.
     * @param fieldDescription how the field to be renamed appears in the outline.
     * @param newNameField the name to change the field to.
     * @throws CoreException
     */
    public static void runFieldRenameTestBasic(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String className, String packageName, String fieldDescription, String newNameField) throws CoreException {
        
        copyFiles(path + "\\src", srcFolder);
        copyFiles(path + "\\oracle", oracleFolder);
        
        selectFieldAndExecuteRenaming(fieldDescription, className, packageName, srcFolder, newNameField, bot);
        
        assertEquals(getOracle(oracleFolder, className), getContentAfterRefactoring(bot));
    }
    
    /**
     * Runs the basic field renaming test on the classNameWithRenaming class and additionally compares
     * the classNameWithoutRenaming as well to its oracle.
     */
    public static void runFieldRenameTestTwoFiles(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String classNameWithRenaming, String packageRenaming, String classNameWithoutRenaming, 
            String packageWithoutRenaming, String fieldDescription, String newNameField) throws CoreException {
        
        runFieldRenameTestBasic(path, srcFolder,oracleFolder, 
                bot,classNameWithRenaming, packageRenaming, fieldDescription, newNameField);
      
        TestUtilsUtil.openEditor(srcFolder.getFolder(packageWithoutRenaming).getFile(classNameWithoutRenaming + 
                JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        assertEquals(getOracle(oracleFolder, classNameWithoutRenaming),getContentAfterRefactoring(bot));

        if (!packageRenaming.equals(packageWithoutRenaming)){
            srcFolder.getFolder(packageWithoutRenaming).delete(true, null);
        }
    }
    
    /**
     * Runs the basic renaming test on the classNameWithRenaming class and additionally compares
     * the classNameWithoutRenaming1 and classNameWithoutRenaming2 to its oracle.
     */
    public static void runFieldRenameTestThreeFiles(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String classNameWithRenaming, String packageRenaming, String classNameWithoutRenaming1, 
            String packageWithoutRenaming1, String classNameWithoutRenaming2, String packageWithoutRenaming2, String fieldDescription, String newNameField) throws CoreException {
        
        runFieldRenameTestBasic(path, srcFolder,oracleFolder, 
                bot,classNameWithRenaming, packageRenaming, fieldDescription, newNameField);
      
        TestUtilsUtil.openEditor(srcFolder.getFolder(packageWithoutRenaming1).getFile(classNameWithoutRenaming1 + 
                JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        assertEquals(getOracle(oracleFolder, classNameWithoutRenaming1),getContentAfterRefactoring(bot));
        
        TestUtilsUtil.openEditor(srcFolder.getFolder(packageWithoutRenaming2).getFile(classNameWithoutRenaming2 + 
                JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        assertEquals(getOracle(oracleFolder, classNameWithoutRenaming2),getContentAfterRefactoring(bot));

        if (!packageRenaming.equals(packageWithoutRenaming1)){
            srcFolder.getFolder(packageWithoutRenaming1).delete(true, null);
        }
        if (!packageRenaming.equals(packageWithoutRenaming2) && !packageWithoutRenaming1.equals(packageWithoutRenaming2)){
            srcFolder.getFolder(packageWithoutRenaming2).delete(true, null);
        }
    }
    
    /**
     * Adds the projects in referencedProjects to the java build path of project.
     */
    public static void setProjectReferences(String project, String[] referencedProjects, SWTWorkbenchBot bot) {
        // select the referencingProject in the package explorer
        SWTBotTreeItem projectToAddReferences = TestUtilsUtil.selectInProjectExplorer(bot, "referencingProject");
        projectToAddReferences.select().pressShortcut(SWT.ALT, SWT.CR);
        
        // select the build path "Java Build Path" and "Projects" tab
        SWTBotShell propertiesDialog = bot.shell("Properties for "+project);      
        TestUtilsUtil.selectInTree(propertiesDialog.bot().tree(), "Java Build Path").click();
    
        SWTBot propertiesDialogBot = propertiesDialog.bot();
        propertiesDialogBot.tabItem("Projects").activate();
        propertiesDialogBot.button("Add...").click();
        
        SWTBotShell projectSelection = bot.shell("Required Project Selection");
        SWTBot projectSelectionBot = projectSelection.bot();
         
       SWTBotTable table = projectSelectionBot.table(0);
       for (String p : referencedProjects){
           table.doubleClick(table.indexOf(p), 0);
           table.pressShortcut(0 , SWT.SPACE);
       }
       
        projectSelectionBot.button(IDialogConstants.OK_LABEL).click();
        propertiesDialogBot.waitUntil(Conditions.shellCloses(projectSelection));
        
        propertiesDialogBot.button(IDialogConstants.OK_LABEL).click();
        bot.waitUntil(Conditions.shellCloses(propertiesDialog));    
    }

    public static IProject createProject(String projectName) throws CoreException, InterruptedException {
        final IJavaProject javaProject = TestUtilsUtil.createJavaProject(projectName);
        final IProject project = javaProject.getProject();
        TestUtilsUtil.createFolder(project,"oracle");
        JMLPreferencesHelper.setProjectJMLProfile(project, JMLPreferencesHelper.getDefaultJMLProfile());
        return project;
    }
    
    public static IProject createProjectWithFiles (String projectName, String path) throws CoreException, InterruptedException {
        final IProject project = createProject(projectName);

        String pathToTests = path + "\\src";
        String pathToOracle = path + "\\oracle";
        
        RefactoringTestUtil.copyFiles(pathToTests, project.getFolder(JDTUtil.getSourceFolderName()));
        RefactoringTestUtil.copyFiles(pathToOracle, project.getFolder("oracle"));
        
        return project;
    }
    
    /**
     * Runs a parameter rename test.
     * 
     * @param path the path of the test files with the sub folders \src and \oracle. 
     * @param srcFolder the folder of the source files to load into eclipse.
     * @param oracleFolder the folder of the oracle.
     * @param bot workbench bot.
     * @param className the class the field to be renamed is in.
     * @param packageName name of the package the class is in.
     * @param methodName how the method which uses the local variable to be renamed appears in the outline.
     * @param newName the parameter's new name.
     * @param offset how much in the text editor to move to the right to select the parameter when the methodName is selected.
     * @throws CoreException
     */
    public static void runParameterRename(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String className, String packageName, String methodName, String newName, int offset) throws CoreException {
        
        copyFiles(path + "\\src", srcFolder);
        copyFiles(path + "\\oracle", oracleFolder);
        
        selectParameterAndExecuteRenaming(methodName, className, packageName, srcFolder, newName, bot, offset);
        
        assertEquals(getOracle(oracleFolder, className), getContentAfterRefactoring(bot));
    }
}