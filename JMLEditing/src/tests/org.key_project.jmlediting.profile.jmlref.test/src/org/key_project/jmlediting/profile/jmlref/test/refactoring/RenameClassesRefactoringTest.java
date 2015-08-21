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

public class RenameClassesRefactoringTest {
    private static final String PROJECT_NAME = "JMLRefactoringRenameTestClasses";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static IFolder srcFolder;
    private static IProject project;
    private static IFolder oracleFolder;
    final String TESTPATH = "data\\template\\refactoringRenameTest\\classes";
    
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
    public void test1JavaAndJMLOneClass() throws CoreException {   
        RefactoringTestUtil.runClassRenameTestBasic(TESTPATH+"\\test1", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "NewClassName");
    }
    
    @Test
    public void test2NoJavaOneClass() throws CoreException {   
        RefactoringTestUtil.runClassRenameTestBasic(TESTPATH+"\\test2", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "NewClassName");
    }
    
    @Test
    public void test3TwoClassesSamePackage() throws CoreException {
        RefactoringTestUtil.runClassRenameTestTwoFiles(TESTPATH+"\\test3", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "OtherClass", "test", "NewClassName");
    }
    
    @Test
    public void test4TwoClassesSamePackageNoJavaChanges() throws CoreException {
        RefactoringTestUtil.runClassRenameTestTwoFiles(TESTPATH+"\\test4", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "OtherClass", "test", "NewClassName");
    }
    
    // TODO: import Statements a problem with current Resolver status.
    //@Test
    public void test5TwoClassesDifferentPackage() throws CoreException {
        RefactoringTestUtil.runClassRenameTestTwoFiles(TESTPATH+"\\test5", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "OtherClass", "otherPackage", "NewClassName");
    }

}
