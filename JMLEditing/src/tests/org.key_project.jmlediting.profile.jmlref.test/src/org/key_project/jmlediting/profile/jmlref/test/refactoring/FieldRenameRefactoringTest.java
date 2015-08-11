package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.junit.After;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class FieldRenameRefactoringTest {
    
    private static final String PROJECT_NAME = "JMLRefactoringRenameTest";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static IFolder srcFolder;
    private static IProject project;
    private static IFolder oracleFolder;
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
        RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test1", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aVeryLongNewName");
    }
    
    @Test
    public void test2AssignableRequiresAndEnsures() throws InterruptedException, CoreException { 
        RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test2", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "tiny");
    }
    
    @Test
    public void test3ThisQualifier() throws InterruptedException, CoreException {  
        RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test3", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test4TwoFilesSamePackageNoChangeInFileTwo() throws InterruptedException, CoreException { 
        RefactoringTestUtil.runFieldRenameTestTwoFiles(TESTPATH+"\\test4", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test5TwoFilesSamePackageFileTwoAccessingMainClass() throws InterruptedException, CoreException {
        RefactoringTestUtil.runFieldRenameTestTwoFiles(TESTPATH+"\\test5", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test6TwoFilesOtherPackageFileTwoAccessingMainClass() throws InterruptedException, CoreException {  
        RefactoringTestUtil.runFieldRenameTestTwoFiles(TESTPATH+"\\test6", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "otherPackage", "balance : int", "aNewName");
    }
    
    @Test
    public void test7TwoFilesMemberAccess() throws InterruptedException, CoreException {  
        RefactoringTestUtil.runFieldRenameTestTwoFiles(TESTPATH+"\\test7", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test8NoJavaChangesInOtherFile() throws InterruptedException, CoreException {
        RefactoringTestUtil.runFieldRenameTestTwoFiles(TESTPATH+"\\test8", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test9NoJavaChangesInTwoOtherFile() throws InterruptedException, CoreException {
        RefactoringTestUtil.runFieldRenameTestThreeFiles(TESTPATH+"\\test9", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "TestClassOther", "test", "TestClassOtherMore", "test", 
                "balance : int", "aNewName");
    }
    
    //TODO: does not work yet
    //@Test
    public void test10Invariant() throws InterruptedException, CoreException {
        RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test10", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName");
    }
    
    @Test
    public void test11thisQualifierMethodFieldName() throws InterruptedException, CoreException {
        RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test11", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : TestClass", "newName");
    }
    
    @Test
    public void test12thisQualifierMethodFieldNameNested() throws InterruptedException, CoreException {
        RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test12", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : TestClass", "newName");
    }
    
    @Test
    public void test13thisQualifierMethodFieldNameNestedChangedOrder() throws InterruptedException, CoreException {
        RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test13", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : TestClass", "newName");
    }
      
     @Test
     public void test14ManyMemberAccesses() throws InterruptedException, CoreException {
         RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test14", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : TestClass", "newName");  
     }
     
     @Test
     public void test15FieldRefAfterMethodCall() throws InterruptedException, CoreException {
         RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test15", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : int", "newName");   
     }
     
     // TODO: Problem with Resolver currently
     //@Test
     public void test16LikeTest15PlusMemberAccess() throws InterruptedException, CoreException {
         RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test16", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : String", "newName");
     }
     
     // TODO:  Problem with Resolver currently
     //@Test
     public void test17LikeTest16WithoutParentheses() throws InterruptedException, CoreException {
         RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test17", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : String", "newName");      
     }
     
     @Test
     public void test18ManyMemberAccessesAndMethodCalls() throws InterruptedException, CoreException {
         RefactoringTestUtil.runFieldRenameTestBasic(TESTPATH+"\\test18", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance", "newName"); 
        }
}
