package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import static org.junit.Assert.assertEquals;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.swt.SWT;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.waits.Conditions;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotShell;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTable;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class FieldRenameRefactoringTest extends org.key_project.jmlediting.profile.jmlref.test.refactoring.RefactoringTestUtil {
    
    private static final String PROJECT_NAME = "JMLRefactoringRenameTest";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static IFolder srcFolder;
    private static IProject project;
    private static IFolder oracleFolder;
    final String CLASS_NAME = "TestClass";
    final String CLASS_NAME_OTHER = "TestClassOther";
    final String CLASS_NAME_MORE = "TestClassOtherMore";
    final String TESTPATH = "data\\template\\refactoringRenameTest";

    @BeforeClass
    public static void initProject() throws CoreException, InterruptedException {
        TestUtilsUtil.closeWelcomeView();
        
        final IJavaProject javaProject = TestUtilsUtil.createJavaProject(PROJECT_NAME);
        project = javaProject.getProject();
        srcFolder = project.getFolder(JDTUtil.getSourceFolderName());      
        oracleFolder = TestUtilsUtil.createFolder(project, "oracle");
        
        JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(), JMLPreferencesHelper.getDefaultJMLProfile());
    }
    
    @After public void deleteTestPackage() throws CoreException {
        srcFolder.getFolder("test").delete(true, null);
    }
    
    @Test
    public void test1SimpleAssignableClause() throws InterruptedException, CoreException {   
        runFieldRenameTestBasic(TESTPATH+"\\test1", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aVeryLongNewName");
    }
    
    @Test
    public void test2AssignableRequiresAndEnsures() throws InterruptedException, CoreException { 
        runFieldRenameTestBasic(TESTPATH+"\\test2", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "tiny");
    }
    
    @Test
    public void test3ThisQualifier() throws InterruptedException, CoreException {  
        runFieldRenameTestBasic(TESTPATH+"\\test3", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test4TwoFilesSamePackageNoChangeInFileTwo() throws InterruptedException, CoreException { 
        runFieldRenameTestTwoFiles(TESTPATH+"\\test4", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test5TwoFilesSamePackageFileTwoAccessingMainClass() throws InterruptedException, CoreException {
        runFieldRenameTestTwoFiles(TESTPATH+"\\test5", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test6TwoFilesOtherPackageFileTwoAccessingMainClass() throws InterruptedException, CoreException {  
        runFieldRenameTestTwoFiles(TESTPATH+"\\test6", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "otherPackage", "balance : int", "aNewName");
    }
    
    @Test
    public void test7TwoFilesMemberAccess() throws InterruptedException, CoreException {  
        runFieldRenameTestTwoFiles(TESTPATH+"\\test7", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test8NoJavaChangesInOtherFile() throws InterruptedException, CoreException {
        runFieldRenameTestTwoFiles(TESTPATH+"\\test8", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test9NoJavaChangesInTwoOtherFile() throws InterruptedException, CoreException {
        runFieldRenameTestThreeFiles(TESTPATH+"\\test9", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "TestClassOtherMore", "test", 
                "balance : int", "aNewName");
    }
    
    //TODO: does not work yet
    //@Test
    public void test10Invariant() throws InterruptedException, CoreException {
        runFieldRenameTestBasic(TESTPATH+"\\test10", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test11thisQualifierMethodFieldName() throws InterruptedException, CoreException {
        runFieldRenameTestBasic(TESTPATH+"\\test11", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : TestClass", "newName");
    }
    
    @Test
    public void test12thisQualifierMethodFieldNameNested() throws InterruptedException, CoreException {
        runFieldRenameTestBasic(TESTPATH+"\\test12", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : TestClass", "newName");
    }
    
    @Test
    public void test13thisQualifierMethodFieldNameNestedChangedOrder() throws InterruptedException, CoreException {
        runFieldRenameTestBasic(TESTPATH+"\\test13", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : TestClass", "newName");
    }
      
     @Test
     public void test14ManyMemberAccesses() throws InterruptedException, CoreException {
         runFieldRenameTestBasic(TESTPATH+"\\test14", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : TestClass", "newName");  
     }
     
     @Test
     public void test15FieldRefAfterMethodCall() throws InterruptedException, CoreException {
         runFieldRenameTestBasic(TESTPATH+"\\test15", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : int", "newName");   
     }
     
     // TODO: Problem with Resolver currently
     //@Test
     public void test16LikeTest15PlusMemberAccess() throws InterruptedException, CoreException {
         runFieldRenameTestBasic(TESTPATH+"\\test16", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : String", "newName");
     }
     
     // TODO:  Problem with Resolver currently
     //@Test
     public void test17LikeTest16WithoutParentheses() throws InterruptedException, CoreException {
         runFieldRenameTestBasic(TESTPATH+"\\test17", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : String", "newName");      
     }
     
     //@Test
     public void test18ManyMemberAccessesAndMethodCalls() throws InterruptedException, CoreException {
         runFieldRenameTestBasic(TESTPATH+"\\test15", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : TestClass<IJavaProject>", "newName"); 
        }
     
     //@Test
     public void test19TwoProjectsOneReference() throws InterruptedException, CoreException {
            
         final IJavaProject referencedProject = TestUtilsUtil.createJavaProject("referencedProject");
         project = referencedProject.getProject();
         IFolder srcFolderReferenced = project.getFolder(JDTUtil.getSourceFolderName());      
         oracleFolder = TestUtilsUtil.createFolder(project, "oracle");
         
         String path = "data\\template\\refactoringRenameTest\\test19\\referencedProject";
         String pathToTests = path + "\\src";
         String pathToOracle = path + "\\oracle";
         
         copyFiles(pathToTests, srcFolderReferenced);
         copyFiles(pathToOracle, oracleFolder);
         
         String oracleStringReferenced = getOracle(oracleFolder, "ReferencedClass");
         
         final IJavaProject referencingProject = TestUtilsUtil.createJavaProject("referencingProject");
         project = referencingProject.getProject();
         IFolder srcFolderReferencing = project.getFolder(JDTUtil.getSourceFolderName());      
         oracleFolder = TestUtilsUtil.createFolder(project, "oracle");
         
         
        path = "data\\template\\refactoringRenameTest\\test19\\referencingProject";
        pathToTests = path + "\\src";
        pathToOracle = path + "\\oracle";
        
        copyFiles(pathToTests, srcFolderReferencing);
        copyFiles(pathToOracle, oracleFolder);
        
        String oracleStringReferencing = getOracle(oracleFolder, "ReferencingClass");
        
        // select the referencingProject in the package explorer
        SWTBotTreeItem projectToAddReferences = TestUtilsUtil.selectInProjectExplorer(bot, "referencingProject");
        //SWTBotTree projectExplorerTree = TestUtilsUtil.getProjectExplorer(bot).bot().tree(); 
        //SWTBotTreeItem projectToAddReferences = TestUtilsUtil.selectInTree(projectExplorerTree, "referencingProject");
        projectToAddReferences.select().pressShortcut(SWT.ALT, SWT.CR);
        
        // select the build path "Java Build Path" and "Projects" tab
        SWTBotShell propertiesDialog = bot.shell("Properties for referencingProject");      
        TestUtilsUtil.selectInTree(propertiesDialog.bot().tree(), "Java Build Path").click();

        SWTBot propertiesDialogBot = propertiesDialog.bot();
        propertiesDialogBot.tabItem("Projects").activate();
        propertiesDialogBot.button("Add...").click();
        
        SWTBotShell projectSelection = bot.shell("Required Project Selection");
        SWTBot projectSelectionBot = projectSelection.bot();
         
       SWTBotTable table = projectSelectionBot.table(0);
       table.doubleClick(projectSelectionBot.table(0).indexOf("referencedProject"), 0);
       
       table.pressShortcut(0 , SWT.SPACE);
       
        projectSelectionBot.button(IDialogConstants.OK_LABEL).click();
        propertiesDialogBot.waitUntil(Conditions.shellCloses(projectSelection));
        
        propertiesDialogBot.button(IDialogConstants.OK_LABEL).click();
        bot.waitUntil(Conditions.shellCloses(propertiesDialog));    
        
        TestUtilsUtil.openEditor(srcFolderReferenced.getFolder("test").getFile("ReferencedClass" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        
        executeRenaming("balance : int", "ReferencedClass", "test", srcFolder, "aNewName", bot);
        
        String afterRenamingReferenced = getContentAfterRefactoring(bot);
        
        assertEquals(oracleStringReferenced,afterRenamingReferenced);
        
        TestUtilsUtil.openEditor(srcFolderReferencing.getFolder("test").getFile("ReferencingClass" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
        String afterRenamingReferencing = getContentAfterRefactoring(bot); 
        assertEquals(oracleStringReferencing,afterRenamingReferencing);
        
        srcFolderReferencing.getProject().delete(true, null);
        srcFolderReferenced.getProject().delete(true, null);
    }
}
