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

public class RenameMethodRefactoringTest {
    
    private static final String PROJECT_NAME = "JMLRefactoringRenameTestMethods";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static IFolder srcFolder;
    private static IProject project;
    private static IJavaProject javaProject;
    private static IFolder oracleFolder;
    final String TESTPATH = "data\\template\\refactoringRenameTest\\methods";

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
        TestUtilsRefactoring.deleteAllPackagesFromFolder(srcFolder);
    }
    
    @Test
    public void test1SameClassNoOther() throws CoreException {   
        TestUtilsRefactoring.runMethodRenameTest(TESTPATH+"\\test1", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "getBalance() : int", "newMethodName", javaProject);
    }
}
