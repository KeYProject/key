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
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.profile.jmlref.test.Activator;
import org.key_project.util.eclipse.BundleUtil;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class FieldRenameRefactoringTest<WaitForShell> {
    
    private static final String PROJECT_NAME = "JMLRefactoringRenameTest";
    //private static final String PACKAGE_NAME = "test";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static IFolder srcFolder;
    private static IProject project;
    private static IFolder oracleFolder;
    final String CLASS_NAME = "TestClass";
    final String CLASS_NAME_OTHER = "TestClassOther";

    @BeforeClass
    public static void initProject() throws CoreException, InterruptedException {
        TestUtilsUtil.closeWelcomeView();
        
        final IJavaProject javaProject = TestUtilsUtil.createJavaProject(PROJECT_NAME);
        project = javaProject.getProject();
        srcFolder = project.getFolder(JDTUtil.getSourceFolderName());      
        oracleFolder = TestUtilsUtil.createFolder(project, "oracle");
        
        JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(), JMLPreferencesHelper.getDefaultJMLProfile());
    }
    
    
    // Get the String representation of the file named oracleName from oracleFolder
    private String getOracle(IFolder oracleFolder, String fileName) throws CoreException {
        
        IFile fileToRead = oracleFolder.getFile(fileName + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT); 

        String oracleString = ResourceUtil.readFrom(fileToRead);  // can throw CoreException
        
        return oracleString;
    }
    
    
    // Extracts files from copyFrom into folderToCopyInto 
    private void copyFiles(String copyFrom, IFolder folderToCopyInto) throws CoreException{
        
        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, copyFrom, folderToCopyInto);
        
        TestUtilsUtil.waitForBuild(); 
    }
    
    // selects className and outlineString in the outline tree, starts renaming and changes field's name to newName
    private void executeRenaming(String className, String fieldToChange, String newName){
        
        SWTBotTree tree = TestUtilsUtil.getOutlineView(bot).bot().tree(); 
        SWTBotTreeItem fieldToRename = TestUtilsUtil.selectInTree(tree, className, fieldToChange);
        fieldToRename.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'R');
                
        // Change variable name in rename dialog
        SWTBotShell renameDialog = bot.shell("Rename Field");      
        SWTBot renameDialogBot = renameDialog.bot();
        renameDialogBot.textWithLabel("New name:").setText(newName);
     
        // start renaming and wait till finished
        renameDialogBot.button(IDialogConstants.OK_LABEL).click();
        bot.waitUntil(Conditions.shellCloses(renameDialog));
    }
 
    // Gets the content from active editor and replaces \n with \r\n 
    // because oracle files were created with windows 
    private String getContentAfterRefactoring(){
        SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();
        
        String content = editor.getText();
        
        editor.close();
        
        return content.replaceAll("(\n)", "\r\n");
    }
    
    @Test
    public void testSimpleAssignableClause() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringRenameTest\\test1";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";
       
        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleString = getOracle(oracleFolder, CLASS_NAME);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

        executeRenaming(CLASS_NAME, "balance : int", "aVeryLongNewName");
        
        String afterRenaming = getContentAfterRefactoring();
        
        // Compare content of editor after renaming to its oracle
        assertEquals(oracleString,afterRenaming);
        
        srcFolder.getFolder("test").delete(true, null);
    }
    
    @Test
    public void testAssignableRequiresAndEnsures() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringRenameTest\\test2";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";
        
        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleString = getOracle(oracleFolder, CLASS_NAME);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        executeRenaming(CLASS_NAME, "balance : int", "tiny");
        
        String afterRenaming = getContentAfterRefactoring();
        
        assertEquals(oracleString,afterRenaming);
        
        srcFolder.getFolder("test").delete(true, null);
    }
    
    @Test
    public void testThisQualifier() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringRenameTest\\test3";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";
        
        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleString = getOracle(oracleFolder, CLASS_NAME);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        executeRenaming(CLASS_NAME, "balance : int", "aNewName");
        
        String afterRenaming = getContentAfterRefactoring();
        
        assertEquals(oracleString,afterRenaming);
        
        srcFolder.getFolder("test").delete(true, null);
    }
    
    @Test
    public void testTwoFilesSamePackageNoChangeInFileTwo() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringRenameTest\\test4";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";
        
        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleString = getOracle(oracleFolder, CLASS_NAME);
        String oracleStringOther = getOracle(oracleFolder, CLASS_NAME_OTHER);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        executeRenaming(CLASS_NAME, "balance : int", "aNewName");
        
        String afterRenaming = getContentAfterRefactoring();
        
        assertEquals(oracleString,afterRenaming);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME_OTHER + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // no renaming done (just get content of active editor)s
        String afterRenamingOther = getContentAfterRefactoring();
        
        assertEquals(oracleStringOther,afterRenamingOther);
        
        srcFolder.getFolder("test").delete(true, null);
    }
    
    @Test
    public void testTwoFilesSamePackageFileTwoAccessingMainClass() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringRenameTest\\test5";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";
        
        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleString = getOracle(oracleFolder, CLASS_NAME);
        String oracleStringOther = getOracle(oracleFolder, CLASS_NAME_OTHER);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        executeRenaming(CLASS_NAME, "balance : int", "aNewName");
        
        String afterRenaming = getContentAfterRefactoring();
        
        assertEquals(oracleString,afterRenaming);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME_OTHER + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // no renaming done (just get content of active editor)s
        String afterRenamingOther = getContentAfterRefactoring();
        
        assertEquals(oracleStringOther,afterRenamingOther);
        
        srcFolder.getFolder("test").delete(true, null);
    }
    
    @Test
    public void testTwoFilesOtherPackageFileTwoAccessingMainClass() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringRenameTest\\test6";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";
        
        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleString = getOracle(oracleFolder, CLASS_NAME);
        String oracleStringOther = getOracle(oracleFolder, CLASS_NAME_OTHER);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        executeRenaming(CLASS_NAME, "balance : int", "aNewName");
        
        String afterRenaming = getContentAfterRefactoring();
        
        assertEquals(oracleString,afterRenaming);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("otherPackage").getFile(CLASS_NAME_OTHER + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // no renaming done (just get content of active editor)s
        String afterRenamingOther = getContentAfterRefactoring();
        
        assertEquals(oracleStringOther,afterRenamingOther);
        
        srcFolder.getFolder("test").delete(true, null);
        srcFolder.getFolder("otherPackage").delete(true, null);
    }
    
    @Test
    public void testTwoFilesMemberAccess() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringRenameTest\\test7";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";
        
        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleString = getOracle(oracleFolder, CLASS_NAME);
        String oracleStringOther = getOracle(oracleFolder, CLASS_NAME_OTHER);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        executeRenaming(CLASS_NAME, "balance : int", "aNewName");
        
        String afterRenaming = getContentAfterRefactoring();
        
        assertEquals(oracleString,afterRenaming);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME_OTHER + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // no renaming done (just get content of active editor)s
        String afterRenamingOther = getContentAfterRefactoring();
        
        assertEquals(oracleStringOther,afterRenamingOther);
        
        srcFolder.getFolder("test").delete(true, null);
    }
    
    @Test
    public void testNoJavaChangesInOtherFile() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringRenameTest\\test8";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";
        
        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleString = getOracle(oracleFolder, CLASS_NAME);
        String oracleStringOther = getOracle(oracleFolder, CLASS_NAME_OTHER);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        executeRenaming(CLASS_NAME, "balance : int", "aNewName");
        
        String afterRenaming = getContentAfterRefactoring();
        
        assertEquals(oracleString,afterRenaming);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME_OTHER + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        // no renaming done (just get content of active editor)s
        String afterRenamingOther = getContentAfterRefactoring();
        
        assertEquals(oracleStringOther,afterRenamingOther);
        
        srcFolder.getFolder("test").delete(true, null);
    }
    
    
    public void testInvariant() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringRenameTest\\test9";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";
        
        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleString = getOracle(oracleFolder, CLASS_NAME);
        
        TestUtilsUtil.openEditor(srcFolder.getFolder("test").getFile(CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        executeRenaming(CLASS_NAME, "balance : int", "aNewName");
        
        String afterRenaming = getContentAfterRefactoring();
        
        assertEquals(oracleString,afterRenaming);
        
        srcFolder.getFolder("test").delete(true, null);
    }
}
