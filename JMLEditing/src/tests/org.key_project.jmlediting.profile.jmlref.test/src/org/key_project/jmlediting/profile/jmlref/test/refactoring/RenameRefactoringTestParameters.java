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

public class RenameRefactoringTestParameters {
    private static final String PROJECT_NAME = "JMLRefactoringRenameTestLocalVariables";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static IFolder srcFolder;
    private static IProject project;
    private static IFolder oracleFolder;
    final String TESTPATH = "data\\template\\refactoringRenameTest\\parameters";

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
    public void test1OneParameter() throws InterruptedException, CoreException {   
        RefactoringTestUtil.runLocalVariableRename(TESTPATH+"\\test1", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "setBalance(int) : void", "aNewName", 6);
    }
    
    @Test
    public void test2TwoParametersFirst() throws InterruptedException, CoreException {   
        RefactoringTestUtil.runLocalVariableRename(TESTPATH+"\\test2", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "setBalance(int, boolean) : void", "aNewName", 7);
    }
    
    @Test
    public void test3TwoParametersSecond() throws InterruptedException, CoreException {   
        RefactoringTestUtil.runLocalVariableRename(TESTPATH+"\\test3", srcFolder, oracleFolder, bot, 
                "TestClass", "test", "setBalance(boolean, int) : void", "aNewName", 26);
    }
}
