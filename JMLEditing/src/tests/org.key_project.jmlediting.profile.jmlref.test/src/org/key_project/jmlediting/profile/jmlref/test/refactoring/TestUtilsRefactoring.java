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
 * Utility class for testing refactoring with SWTBot.
 * 
 * @author Robert Heimbach
 *
 */
public class TestUtilsRefactoring {

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
     * Unifies line breaks when copying.
     * 
     * @param copyFrom the path as a string to a folder in a bundle with the content to copy.
     * @param folderToCopyInto target in workspace to copy into.
     * @throws CoreException
     */
    public static void copyFiles(String copyFrom, IFolder folderToCopyInto) throws CoreException{
        
        BundleUtil.extractFromBundleToWorkspace(org.key_project.jmlediting.profile.jmlref.test.Activator.PLUGIN_ID, copyFrom, folderToCopyInto, true);
        
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
        
        return content;
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
     * @param nameOfShell either "Rename Field" or "Rename Method" expected.
     */
    public static void selectElementInOutlineAndExecuteRenaming(String fieldToChange, String className, String packageName, IFolder srcFolder, String newName, SWTWorkbenchBot bot, String nameOfShell){
        
        TestUtilsUtil.openEditor(srcFolder.getFolder(packageName).getFile(className + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // select the fieldToChange in the outline view of the bot
        SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree(); 
        SWTBotTreeItem fieldToRename = TestUtilsUtil.selectInTree(tree, className, fieldToChange);
        
        fieldToRename.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'R');
                
        // Change variable name in rename dialog
        SWTBotShell renameDialog = bot.shell(nameOfShell);  
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
     * 
     * @param projectName
     * @param packageName
     * @param srcFolder
     * @param newPackageName
     * @param bot
     * @param activateSubpackageOption
     */
    public static void selectPackageAndExecuteRenaming(String projectName,
            String packageName, IFolder srcFolder, String newPackageName,
            SWTWorkbenchBot bot, Boolean activateSubpackageOption) {
                
        SWTBotTreeItem packageToRename = TestUtilsUtil.selectInProjectExplorer(bot, projectName, "src", packageName);
        
        packageToRename.pressShortcut(SWT.ALT | SWT.SHIFT, 'R');
        
        SWTBotShell renameDialog = bot.shell("Rename Package");      
        
        // Check if the "Rename subpackages" option if correctly set
        SWTBot renameBot = renameDialog.bot();
        SWTBotCheckBox checkBox = renameBot.checkBox("Rename subpackages");
        
        // activate if needed but not set || deactivate if wrongly set
        if ((activateSubpackageOption && !checkBox.isChecked()) 
                || (!activateSubpackageOption && checkBox.isChecked()) ) {
            checkBox.click();
        }
        
        setNewElementName(newPackageName, bot, renameDialog); 
    }
    
    /**
     * Selects the class named className in the outline view of the SWTWorkbenchBot bot and
     * activates renaming to newClassName.
     * 
     * @param className the class to be renamed (without .java file ending).
     * @param packageName name of the package the class is in.
     * @param srcFolder sourceFolder of the class className.
     * @param newClassName the new name of the class.
     * @param bot SWTWorkbenchBot to select the outline view from.
     */
    public static void selectClassAndExecuteRenaming(String className,
            String packageName, IFolder srcFolder, String newClassName,
            SWTWorkbenchBot bot) {
        
        TestUtilsUtil.openEditor(srcFolder.getFolder(packageName).getFile(className + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
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


    /** Selects an element in the outline and moved it to another class.
     * 
     * @param srcFolder folder the source class is in.
     * @param fromclass class with the element which should be moved.
     * @param fromPackage package the source class is in.
     * @param destclass class to move the element to.
     * @param destpackage package the destination class is in.
     * @param elementDescription how the element to be moved appears in the outline.
     * @param bot workbench bot.
     */
    public static void selectElementInOutlineAndMove(IFolder srcFolder, String fromclass, String fromPackage, String destclass, String destpackage, String elementDescription, SWTWorkbenchBot bot){

        TestUtilsUtil.openEditor(srcFolder.getFolder(fromPackage).getFile(fromclass + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree(); 
        SWTBotTreeItem fieldToMove = TestUtilsUtil.selectInTree(tree, fromclass, elementDescription);
        fieldToMove.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'V');
        SWTBotShell moveDialog = bot.shell("Move Static Members"); 
        SWTBot moveDialogBot = moveDialog.bot();
        moveDialogBot.comboBox().setText(destpackage+"."+destclass);
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
     * @param bot swtworkbench bot.
     */
    public static void selectClassAndMove(String projectNameSrc, String className, String packageFrom, String projectTo, String packageTo, SWTWorkbenchBot bot){

        SWTBotTree tree = TestUtilsUtil.getProjectExplorer(bot).bot().tree(); 
        SWTBotTreeItem classToMove = TestUtilsUtil.selectInTree(tree, projectNameSrc,"src",packageFrom,className+".java");

        classToMove.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'V');

        // Change variable name in rename dialog
        SWTBotShell moveDialog = bot.shell("Move");      
        SWTBot moveDialogBot = moveDialog.bot();
        SWTBotTree moveTree = moveDialogBot.tree();
        TestUtilsUtil.selectInTree(moveTree, projectTo,"src",packageTo);

        // start renaming and wait till finished
        moveDialogBot.button(IDialogConstants.OK_LABEL).click();

        bot.waitUntil(Conditions.shellCloses(moveDialog));
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
     * @param outlineAppearance how the field to be renamed appears in the outline.
     * @param newName the new name to change to.
     * @param javaProject project the classes are in.
     * @throws CoreException
     */
    public static void runFieldRenameTest(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String className, String packageName, String outlineAppearance, String newName, IJavaProject javaProject) throws CoreException {
        
        copyFiles(path + "\\src", srcFolder);
        copyFiles(path + "\\oracle", oracleFolder);
        
        selectElementInOutlineAndExecuteRenaming(outlineAppearance, className, packageName, srcFolder, newName, bot, "Rename Field");
        
        compareAllFilesInProjectToOracle(javaProject, oracleFolder, bot);
    }
    
    /**
     * Runs a basic method rename test. That is, only one project, one file and renaming of one field.
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
     */
    public static void runMethodRenameTest(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String className, String packageName, String outlineAppearance, String newName, IJavaProject javaProject) throws CoreException {
        
        copyFiles(path + "\\src", srcFolder);
        copyFiles(path + "\\oracle", oracleFolder);
        
        selectElementInOutlineAndExecuteRenaming(outlineAppearance, className, packageName, srcFolder, newName, bot, "Rename Method");
        
        compareAllFilesInProjectToOracle(javaProject, oracleFolder, bot);
    }
    
    /**
     * Runs a basic class rename test. That is, only one project and one class.
     * 
     * @param path the path of the test files with the sub folders \src and \oracle. 
     * @param srcFolder the folder of the source files to load into eclipse.
     * @param oracleFolder the folder of the oracle.
     * @param bot workbench bot.
     * @param className the class the field to be renamed is in.
     * @param packageName name of the package the class is in.
     * @param newClassName the name to change the field to.
     * @throws CoreException
     */
    public static void runClassRenameTestBasic(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String className, String packageName, String newClassName, IJavaProject javaProject) throws CoreException {
        
        copyFiles(path + "\\src", srcFolder);
        copyFiles(path + "\\oracle", oracleFolder);
        
        selectClassAndExecuteRenaming(className, packageName, srcFolder, newClassName, bot);
        
        compareAllFilesInProjectToOracle(javaProject, oracleFolder, bot);
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
    public static void runParameterRenameTest(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String className, String packageName, String methodName, String newName, int offset) throws CoreException {
        
        copyFiles(path + "\\src", srcFolder);
        copyFiles(path + "\\oracle", oracleFolder);
        
        selectParameterAndExecuteRenaming(methodName, className, packageName, srcFolder, newName, bot, offset);
        
        assertEquals(getOracle(oracleFolder, className), getContentAfterRefactoring(bot));
    }
    
    /**
     * 
     * @param path
     * @param srcFolder
     * @param oracleFolder
     * @param bot
     * @param packageName
     * @param newPackageName
     * @param project
     * @param renameSubpackages
     * @throws CoreException
     */
    public static void runPackageRenameTest(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String packageName, String newPackageName, IJavaProject project, Boolean renameSubpackages) throws CoreException {
        
        copyFiles(path + "\\src", srcFolder);
        copyFiles(path + "\\oracle", oracleFolder);

        selectPackageAndExecuteRenaming(project.getElementName(), packageName, srcFolder, newPackageName, bot, renameSubpackages);
        
        compareAllFilesInProjectToOracle(project, oracleFolder, bot);
    }
    
    /**
     * Runs a basic field or method move test. The element to be moved is selected in the outline.
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
    public static void runMoveOutlineElementTest(String path, IFolder srcFolder, IFolder oracleFolder, 
            SWTWorkbenchBot bot, String classNameMoveFrom, String packageName, String elementDescription, String classNameMoveTo, String packageTo, IJavaProject javaProject) throws CoreException {
        
        copyFiles(path + "\\src", srcFolder);
        copyFiles(path + "\\oracle", oracleFolder);
        
        selectElementInOutlineAndMove(srcFolder, classNameMoveFrom, packageName, classNameMoveTo, packageTo, elementDescription, bot);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("mainpack").getFile("Main" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // Movements of the JDT will result in added tabs in front of the method / field to get the right indentation 
        assertEquals(getOracle(oracleFolder, "Main"), getContentAfterRefactoring(bot).replace("\t","    "));
    }
    
    /**
     * Runs a move class test. A class is selected in the package explorer and moved.
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
            SWTWorkbenchBot bot, String classNameMoveFrom, String packageFrom, String packageTo, IJavaProject javaProject) throws CoreException {
        
        copyFiles(path + "\\src", srcFolder);
        copyFiles(path + "\\oracle", oracleFolder);
        
        String projectName = javaProject.getElementName();
        
        selectClassAndMove(projectName, classNameMoveFrom, packageFrom, projectName, packageTo, bot);
        
        compareFileToOracle(srcFolder, oracleFolder, "mainpack", "Main", bot);
    }
    
    public static void compareFileToOracle(IFolder srcFolder, IFolder oracleFolder, String packageName, String classNameToCompare, SWTWorkbenchBot bot) throws CoreException{
        
        TestUtilsUtil.openEditor(srcFolder.getFolder(packageName).getFile(classNameToCompare + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // Movements of the JDT will result in added tabs in front of the method / field to get the right indentation .replace("\t","    ")
        assertEquals(getOracle(oracleFolder, classNameToCompare), getContentAfterRefactoring(bot));
    }
    
    
    /**
     * Compares all files of a given project to the files in a given folder of oracle files.
     * 
     * @param project project which files should be compared.
     * @param oracleFolder folder which contains the oracle files.
     * @param bot {@link SWTWorkbenchBot} to make the actions.
     * @throws CoreException thrown if the packages of the project could not be accessed.
     */
    public static void compareAllFilesInProjectToOracle(IJavaProject project, IFolder oracleFolder, SWTWorkbenchBot bot) throws CoreException {
        for (IPackageFragment fragment : RefactoringUtil.getAllPackageFragmentsContainingSources(project)) {
            for (ICompilationUnit unit : fragment.getCompilationUnits()) {
                assertEquals(getOracle(oracleFolder, unit.getElementName()), unit.getSource());
            }
        }
    }

    /**
     * Adds the projects in referencedProjects to the java build path of project.
     * 
     * @param projectToAddTo project which build path needs additional entries.
     * @param referencedProjects other projects to add to the build path of projectToAddTo.
     * @param bot {@link SWTWorkbenchBot} to make the required UI actions.
     */
    public static void setProjectReferences(String projectToAddTo, String[] referencedProjects, SWTWorkbenchBot bot) {
        // select the referencingProject in the package explorer
        
//        SWTBotView viewBot = TestUtilsUtil.getProjectExplorer(bot);
//        SWTBotTree tree = viewBot.bot().tree();
//        for (SWTBotTreeItem item : tree.getAllItems()){
//            System.out.println(item.getText());
//        }
//        
//        System.out.println("searching for "+projectToAddTo);
        
        SWTBotTreeItem projectToAddReferences = TestUtilsUtil.selectInProjectExplorer(bot, projectToAddTo);
        projectToAddReferences.select().pressShortcut(SWT.ALT, SWT.CR);
        
        // select the build path "Java Build Path" and "Projects" tab
        SWTBotShell propertiesDialog = bot.shell("Properties for "+projectToAddTo);      
        TestUtilsUtil.selectInTree(propertiesDialog.bot().tree(), "Java Build Path").click();
    
        SWTBot propertiesDialogBot = propertiesDialog.bot();
        propertiesDialogBot.tabItem("Projects").activate();
        propertiesDialogBot.button("Add...").click();
        
        SWTBotShell projectSelection = bot.shell("Required Project Selection");
        SWTBot projectSelectionBot = projectSelection.bot();
        
        // select the projects to add in the shown table 
        SWTBotTable table = projectSelectionBot.table(0);
        for (String p : referencedProjects){
            table.doubleClick(table.indexOf(p), 0);
            table.pressShortcut(0 , SWT.SPACE);
        }
       
        // finish the process.
        projectSelectionBot.button(IDialogConstants.OK_LABEL).click();
        propertiesDialogBot.waitUntil(Conditions.shellCloses(projectSelection));
        
        propertiesDialogBot.button(IDialogConstants.OK_LABEL).click();
        bot.waitUntil(Conditions.shellCloses(propertiesDialog));    
    }

    /**
     * Creates a project, sets the JML profile to the default JML profile and creates a folder called "oracle".
     * 
     * @param projectName name of the project to create.
     * @return the created {@link IProject}.
     * @throws CoreException thrown if the project could not be created.
     * @throws InterruptedException thrown if the creation of the project is interrupted.
     */
    public static IProject setupProjectAndOracle(String projectName) throws CoreException, InterruptedException {
        final IJavaProject javaProject = TestUtilsUtil.createJavaProject(projectName);
        final IProject project = javaProject.getProject();
        TestUtilsUtil.createFolder(project,"oracle");
        JMLPreferencesHelper.setProjectJMLProfile(project, JMLPreferencesHelper.getDefaultJMLProfile());
        return project;
    }
    
    /**
     * Creates a project with a folder called "oracle" and copies the needed files for testing
     * into the "src" and "oracle" folder of the project.
     * 
     * @param projectName name of the project to create.
     * @param path path of the file system where the files to copy are. Expects a "src" and "oracle" folder.
     * @return the created {@link IProject}.
     * @throws CoreException thrown when the project could not be created.
     * @throws InterruptedException thrown if the project creation was interrupted.
     */
    public static IProject createProjectWithFiles (String projectName, String path) throws CoreException, InterruptedException {
        final IProject project = setupProjectAndOracle(projectName);

        String pathToTests = path + "\\src";
        String pathToOracle = path + "\\oracle";
        
        TestUtilsRefactoring.copyFiles(pathToTests, project.getFolder(JDTUtil.getSourceFolderName()));
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
            if (member instanceof IFolder) {
                folder.getFolder(member.getName()).delete(false, null);
            }
        }
    }
}