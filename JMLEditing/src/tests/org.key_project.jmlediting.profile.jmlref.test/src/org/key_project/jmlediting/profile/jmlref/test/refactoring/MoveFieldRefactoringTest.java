package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import static org.junit.Assert.assertEquals;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class MoveFieldRefactoringTest {

    private static final String PROJECT_NAME = "MoveFieldRefactoringTest";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

    private static IFolder srcFolder;
    private static IProject project;
    private static IFolder oracleFolder;

    private static IJavaProject javaProject;
    final String REF_CLASS_NAME = "Main";
    final String CLASS_NAME_MOVE_FROM = "Settings";
    final String CLASS_NAME_MOVE_TO = "Params";
    final String FIELD_TO_MOVE="x : int";
    final String TESTPATH = "data\\template\\refactoringMoveTest\\moveFieldTest";

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

    @AfterClass
    public static void deleteProject() throws CoreException {
        project.delete(true, null);
    }
    
    @Test
    public void test1SimpleMove() throws InterruptedException, CoreException {
        
        TestUtilsRefactoring.runMoveOutlineElementTest(TESTPATH+"\\test1", srcFolder, oracleFolder, bot, 
                CLASS_NAME_MOVE_FROM, "test1p1", FIELD_TO_MOVE, CLASS_NAME_MOVE_TO, "test1p2", javaProject); 
    }
   
    @Test
    public void test2MoveComplexPackage() throws InterruptedException, CoreException {
        
        TestUtilsRefactoring.runMoveOutlineElementTest(TESTPATH+"\\test2", srcFolder, oracleFolder, bot, 
                CLASS_NAME_MOVE_FROM, "test2p1", FIELD_TO_MOVE, CLASS_NAME_MOVE_TO, "test2p2.complex", javaProject);
    }
    
    @Test
    public void test3MoveUseOps() throws InterruptedException, CoreException {
        
        TestUtilsRefactoring.runMoveOutlineElementTest(TESTPATH+"\\test3", srcFolder, oracleFolder, bot, 
                CLASS_NAME_MOVE_FROM, "test3p1", FIELD_TO_MOVE, CLASS_NAME_MOVE_TO, "test3p2", javaProject);
    } 
    
    @Test
    public void test4MoveComplexUseOpsBackwards() throws InterruptedException, CoreException {

        TestUtilsRefactoring.runMoveOutlineElementTest(TESTPATH+"\\test4", srcFolder, oracleFolder, bot, 
                CLASS_NAME_MOVE_TO, "test4p2\\complex", FIELD_TO_MOVE, CLASS_NAME_MOVE_FROM, "test4p1", javaProject);
    }
    
    @Test
    public void test5MoveIntoClassWithReferences() throws InterruptedException, CoreException {
        
        TestUtilsRefactoring.runMoveOutlineElementTest(TESTPATH+"\\test5", srcFolder, oracleFolder, bot, 
                CLASS_NAME_MOVE_FROM, "test1p1", FIELD_TO_MOVE, "Main", "mainpack", javaProject); 
    }
    
    @Test
    public void test6MoveIntoAnotherProjectFromSamePackageNoImport() throws InterruptedException, CoreException {
       // Create projects and set references
       final IProject projectSrc = TestUtilsRefactoring.createProjectWithFiles("projectSrc", "data\\template\\refactoringMoveTest\\moveFieldTest\\test6\\projectSrc");
       
       final IProject projectDest = TestUtilsRefactoring.createProjectWithFiles("projectDest", "data\\template\\refactoringMoveTest\\moveFieldTest\\test6\\projectDest");
       
       TestUtilsRefactoring.setProjectReferences("projectSrc", new String[]{"projectDest"}, bot);
       
       // Execute Move and Check
       TestUtilsRefactoring.selectElementInOutlineAndMove(projectSrc.getFolder(JDTUtil.getSourceFolderName()), "Other", "mainpack", "Dest", "destPackage", "balance : int", bot);
       
       TestUtilsUtil.openEditor(projectSrc.getFolder(JDTUtil.getSourceFolderName()).getFolder("mainpack").getFile("Main" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

       assertEquals(TestUtilsRefactoring.getOracle(projectSrc.getFolder("oracle"), "Main"),TestUtilsRefactoring.getContentAfterRefactoring(bot));

       projectSrc.delete(true, null);
       projectDest.delete(true, null);
    }
    
    @Test
    public void test7TwoProjectsMoveFieldNotReferences() throws InterruptedException, CoreException {
       // Create projects and set references
       final IProject projectSrc = TestUtilsRefactoring.createProjectWithFiles("projectSrc", "data\\template\\refactoringMoveTest\\moveFieldTest\\test7\\projectSrc");
       
       final IProject projectDest = TestUtilsRefactoring.createProjectWithFiles("projectDest", "data\\template\\refactoringMoveTest\\moveFieldTest\\test7\\projectDest");
       
       TestUtilsRefactoring.setProjectReferences("projectSrc", new String[]{"projectDest"}, bot);
       
       // Execute Move and Check
       TestUtilsRefactoring.selectElementInOutlineAndMove(projectSrc.getFolder(JDTUtil.getSourceFolderName()), "Other", "mainpack", "Dest", "destPackage", "balance : int", bot);
       
       TestUtilsUtil.openEditor(projectSrc.getFolder(JDTUtil.getSourceFolderName()).getFolder("mainpack").getFile("Main" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

       assertEquals(TestUtilsRefactoring.getOracle(projectSrc.getFolder("oracle"), "Main"),TestUtilsRefactoring.getContentAfterRefactoring(bot));

       projectSrc.delete(true, null);
       projectDest.delete(true, null);
    }
    
    @Test
    public void test8TwoProjectsClassImportedMovedIntoOtherFolder() throws InterruptedException, CoreException {
       // Create projects and set references
       final IProject projectSrc = TestUtilsRefactoring.createProjectWithFiles("projectSrc", "data\\template\\refactoringMoveTest\\moveFieldTest\\test8\\projectSrc");
       
       final IProject projectDest = TestUtilsRefactoring.createProjectWithFiles("projectDest", "data\\template\\refactoringMoveTest\\moveFieldTest\\test8\\projectDest");
       
       TestUtilsRefactoring.setProjectReferences("projectSrc", new String[]{"projectDest"}, bot);
       
       // Execute Move and Check
       TestUtilsRefactoring.selectElementInOutlineAndMove(projectDest.getFolder(JDTUtil.getSourceFolderName()), "Other", "destPackage", "Dest", "destPackage", "balance : int", bot);
       
       TestUtilsUtil.openEditor(projectSrc.getFolder(JDTUtil.getSourceFolderName()).getFolder("mainpack").getFile("Main" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

       assertEquals(TestUtilsRefactoring.getOracle(projectSrc.getFolder("oracle"), "Main"),TestUtilsRefactoring.getContentAfterRefactoring(bot));

       projectSrc.delete(true, null);
       projectDest.delete(true, null);
    }
    
    @Test
    public void test9TwoProjectsImportedViaStarOperator() throws InterruptedException, CoreException {
       // Create projects and set references
       final IProject projectSrc = TestUtilsRefactoring.createProjectWithFiles("projectSrc", "data\\template\\refactoringMoveTest\\moveFieldTest\\test9\\projectSrc");
       
       final IProject projectDest = TestUtilsRefactoring.createProjectWithFiles("projectDest", "data\\template\\refactoringMoveTest\\moveFieldTest\\test9\\projectDest");
       
       TestUtilsRefactoring.setProjectReferences("projectSrc", new String[]{"projectDest"}, bot);
       
       // Execute Move and Check
       TestUtilsRefactoring.selectElementInOutlineAndMove(projectDest.getFolder(JDTUtil.getSourceFolderName()), "Other", "destPackage", "Dest", "destPackage", "balance : int", bot);
       
       TestUtilsUtil.openEditor(projectSrc.getFolder(JDTUtil.getSourceFolderName()).getFolder("mainpack").getFile("Main" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

       assertEquals(TestUtilsRefactoring.getOracle(projectSrc.getFolder("oracle"), "Main"),TestUtilsRefactoring.getContentAfterRefactoring(bot));

       projectSrc.delete(true, null);
       projectDest.delete(true, null);
    }
}
