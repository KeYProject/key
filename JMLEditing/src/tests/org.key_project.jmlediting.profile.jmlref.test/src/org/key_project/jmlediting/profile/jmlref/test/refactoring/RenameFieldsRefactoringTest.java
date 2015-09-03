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

public class RenameFieldsRefactoringTest {
    
    private static final String PROJECT_NAME = "JMLRefactoringRenameTestFields";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static IFolder srcFolder;
    private static IProject project;
    private static IJavaProject javaProject;
    private static IFolder oracleFolder;
    final String TESTPATH = "data\\template\\refactoringRenameTest\\fields";

    @BeforeClass
    public static void initProject() throws CoreException, InterruptedException {
        TestUtilsUtil.closeWelcomeView();
        
        javaProject = TestUtilsUtil.createJavaProject(PROJECT_NAME);
        project = javaProject.getProject();
        srcFolder = project.getFolder(JDTUtil.getSourceFolderName());      
        oracleFolder = TestUtilsUtil.createFolder(project, "oracle");
        
        JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(), JMLPreferencesHelper.getDefaultJMLProfile());
    }
    
    @After public void deleteTestPackage() throws CoreException {
        RefactoringTestUtil.deleteAllPackagesFromFolder(srcFolder);
    }
    
    @Test
    public void test1SimpleAssignableClause() throws CoreException {   
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test1", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aVeryLongNewName", javaProject);
    }
    
    @Test
    public void test2AssignableRequiresAndEnsures() throws CoreException { 
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test2", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "tiny", javaProject);
    }
    
    @Test
    public void test3ThisQualifier() throws CoreException {  
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test3", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName", javaProject);
    }
    
    @Test
    public void test4TwoFilesSamePackageNoChangeInFileTwo() throws CoreException { 
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test4", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName", javaProject);
    }
    
    @Test
    public void test5TwoFilesSamePackageFileTwoAccessingMainClass() throws CoreException {
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test5", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName", javaProject);
    }
    
    @Test
    public void test6TwoFilesOtherPackageFileTwoAccessingMainClass() throws CoreException {  
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test6", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName", javaProject);
    }
    
    @Test
    public void test7TwoFilesMemberAccess() throws CoreException {  
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test7", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName", javaProject);
    }
    
    @Test
    public void test8NoJavaChangesInOtherFile() throws CoreException {
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test8", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName", javaProject);
    }
    
    @Test
    public void test9NoJavaChangesInTwoOtherFile() throws CoreException {
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test9", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName", javaProject);
    }
    
    //TODO: does not work yet
    //@Test
    public void test10Invariant() throws CoreException {
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test10", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : int", "aNewName", javaProject);
    }
    
    @Test
    public void test11thisQualifierMethodFieldName() throws CoreException {
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test11", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : TestClass", "newName", javaProject);
    }
    
    @Test
    public void test12thisQualifierMethodFieldNameNested() throws CoreException {
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test12", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : TestClass", "newName", javaProject);
    }
    
    @Test
    public void test13thisQualifierMethodFieldNameNestedChangedOrder() throws CoreException {
        RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test13", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "balance : TestClass", "newName", javaProject);
    }
      
     @Test
     public void test14ManyMemberAccesses() throws CoreException {
         RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test14", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : TestClass", "newName", javaProject);  
     }
     
     @Test
     public void test15FieldRefAfterMethodCall() throws CoreException {
         RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test15", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : int", "newName", javaProject);   
     }
     
     // TODO: Problem with Resolver currently
     //@Test
     public void test16LikeTest15PlusMemberAccess() throws CoreException {
         RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test16", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : String", "newName", javaProject);
     }
     
     // TODO:  Problem with Resolver currently
     //@Test
     public void test17LikeTest16WithoutParentheses() throws CoreException {
         RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test17", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : String", "newName", javaProject);      
     }
     
     @Test
     public void test18ManyMemberAccessesAndMethodCalls() throws CoreException {
         RefactoringTestUtil.runFieldRenameTest(TESTPATH+"\\test18", srcFolder, oracleFolder, bot, 
                 "TestClass", "test", "balance : int", "newName", javaProject); 
        }
}
