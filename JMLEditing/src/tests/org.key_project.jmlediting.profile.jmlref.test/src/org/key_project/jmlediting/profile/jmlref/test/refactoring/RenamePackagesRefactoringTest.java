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

public class RenamePackagesRefactoringTest {
    
    private static final String PROJECT_NAME = "JMLRefactoringRenameTestPackages";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static IFolder srcFolder;
    private static IProject project;
    private static IFolder oracleFolder;

    private static IJavaProject javaProject;
    final String TESTPATH = "data\\template\\refactoringRenameTest\\packages";

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
    
    //@Test
    public void test1OneClassInOnePackage() throws CoreException {   
        TestUtilsRefactoring.runPackageRenameTest(TESTPATH+"\\test1", srcFolder, oracleFolder, bot, 
                 "test", "newPackageName", javaProject, false);
    }
    
    //@Test
    public void test2TwoClassesInSamePackage() throws CoreException {   
        TestUtilsRefactoring.runPackageRenameTest(TESTPATH+"\\test2", srcFolder, oracleFolder, bot, 
                 "test", "newPackageName", javaProject, false);
    }
    
    //@Test
    public void test3TwoClassesInSamePackageMoreReferences() throws CoreException {   
        TestUtilsRefactoring.runPackageRenameTest(TESTPATH+"\\test3", srcFolder, oracleFolder, bot, 
                 "test", "newPackageName", javaProject, false);
    }
    
    //@Test
    public void test4TwoPackagesTwoClassesInRenamedPackage() throws CoreException {   
        TestUtilsRefactoring.runPackageRenameTest(TESTPATH+"\\test4", srcFolder, oracleFolder, bot, 
                 "test", "newPackageName", javaProject, false);
    }
    
    //@Test
    public void test5RenamingOfSubpackage() throws CoreException {   
        TestUtilsRefactoring.runPackageRenameTest(TESTPATH+"\\test5", srcFolder, oracleFolder, bot, 
                 "test.subpackage", "test.newPackageName", javaProject, false);
    }
    
    //@Test
    public void test6RenamingOfSubpackageAndReferenceToClassInParentPackage() throws CoreException {   
        TestUtilsRefactoring.runPackageRenameTest(TESTPATH+"\\test6", srcFolder, oracleFolder, bot, 
                 "test.subpackage", "test.newPackageName", javaProject, false);
    }
    
    @Test
    public void test7RenameParentPackageWithRenameSubpackagesOptionActivated() throws CoreException {   
        TestUtilsRefactoring.runPackageRenameTest(TESTPATH+"\\test7", srcFolder, oracleFolder, bot, 
                 "test", "newPackageName", javaProject, true);
    }
    
    @Test
    public void test8RenameParentPackageOnly() throws CoreException {   
        TestUtilsRefactoring.runPackageRenameTest(TESTPATH+"\\test8", srcFolder, oracleFolder, bot, 
                 "test", "newPackageName", javaProject, false);
    }
}
