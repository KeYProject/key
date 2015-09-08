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

public class MoveClassRefactoringTest{

    private static final String PROJECT_NAME = "JMLRefactoringMoveTest";
    //private static final String PACKAGE_NAME = "test";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

    private static IFolder srcFolder;
    private static IProject project;
    private static IFolder oracleFolder;
    final String REF_CLASS_NAME = "Main";
    final String CLASS_NAME_MOVE = "Settings";


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

        BundleUtil.extractFromBundleToWorkspace(Activator.PLUGIN_ID, copyFrom, folderToCopyInto, true);

        TestUtilsUtil.waitForBuild(); 
    }

    // selects className and outlineString in the outline tree, starts renaming and changes field's name to newName
    private void executeMoving(String className, String moveFrom, String moveTo){

        SWTBotTree tree = TestUtilsUtil.getProjectExplorer(bot).bot().tree(); 
        SWTBotTreeItem fieldToMove = TestUtilsUtil.selectInTree(tree, "JMLRefactoringMoveTest","src",moveFrom,className+".java");

        fieldToMove.select().pressShortcut(SWT.ALT | SWT.SHIFT, 'V');

        // Change variable name in rename dialog
        SWTBotShell moveDialog = bot.shell("Move");      
        SWTBot moveDialogBot = moveDialog.bot();
        SWTBotTree moveTree = moveDialogBot.tree();
        TestUtilsUtil.selectInTree(moveTree, "JMLRefactoringMoveTest","src",moveTo);

        // start renaming and wait till finished
        moveDialogBot.button(IDialogConstants.OK_LABEL).click();
        //TODO:: press Continue if dialog pops up

        //SWTBotShell moveChildDialog = moveDialog.bot().shell("Move", moveDialog.widget);

        //SWTBot moveChildDialogBot = moveChildDialog.bot();
        //moveChildDialogBot.button("Continue").click();
        bot.waitUntil(Conditions.shellCloses(moveDialog));
    }

    // Gets the content from active editor and replaces \n with \r\n 
    // because oracle files were created with windows 
    private String getContentAfterRefactoring(){
        SWTBotEclipseEditor editor = bot.activeEditor().toTextEditor();

        String content = editor.getText();

        editor.close();

        return content;
    }


    @Test
    public void test1SimpleMove() throws InterruptedException, CoreException {

        final String path = "data\\template\\refactoringMoveTest\\moveClassTest\\test1";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";

        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);

        String oracleString = getOracle(oracleFolder, REF_CLASS_NAME);

        TestUtilsUtil.openEditor(srcFolder.getFolder("mainpack").getFile(REF_CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        executeMoving(CLASS_NAME_MOVE, "test1p1", "test1p2");

        String afterRenaming = getContentAfterRefactoring();
        assertEquals(oracleString,afterRenaming);

        srcFolder.delete(true, null);
        oracleFolder.delete(true, null);
        
    }

    @Test
    public void test2MoveComplexPackage() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringMoveTest\\moveClassTest\\test2";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";

        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);

        String oracleString = getOracle(oracleFolder, REF_CLASS_NAME);

        TestUtilsUtil.openEditor(srcFolder.getFolder("mainpack").getFile(REF_CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        executeMoving(CLASS_NAME_MOVE, "test2p1","test2p2.complex");

        String afterRenaming = getContentAfterRefactoring();
        assertEquals(oracleString,afterRenaming);

        srcFolder.delete(true, null);
        oracleFolder.delete(true, null);
    }

    @Test
    public void test3MoveUseOps() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringMoveTest\\moveClassTest\\test3";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";

        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);

        String oracleString = getOracle(oracleFolder, REF_CLASS_NAME);

        TestUtilsUtil.openEditor(srcFolder.getFolder("mainpack").getFile(REF_CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        executeMoving(CLASS_NAME_MOVE, "test3p1","test3p2");

        String afterRenaming = getContentAfterRefactoring();
        assertEquals(oracleString,afterRenaming);

        srcFolder.delete(true, null);
        oracleFolder.delete(true, null);
    } 
    
    @Test
    public void test4MoveComplexUseOpsBackwards() throws InterruptedException, CoreException {
        
        final String path = "data\\template\\refactoringMoveTest\\moveClassTest\\test4";
        final String pathToTests = path + "\\src";
        final String pathToOracle = path + "\\oracle";

        copyFiles(pathToTests, srcFolder);
        copyFiles(pathToOracle, oracleFolder);

        String oracleString = getOracle(oracleFolder, REF_CLASS_NAME);

        TestUtilsUtil.openEditor(srcFolder.getFolder("mainpack").getFile(REF_CLASS_NAME + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        executeMoving(CLASS_NAME_MOVE, "test4p2.complex","test4p1");

        String afterRenaming = getContentAfterRefactoring();
        assertEquals(oracleString,afterRenaming);

        srcFolder.delete(true, null);
        oracleFolder.delete(true, null);
    }
}
