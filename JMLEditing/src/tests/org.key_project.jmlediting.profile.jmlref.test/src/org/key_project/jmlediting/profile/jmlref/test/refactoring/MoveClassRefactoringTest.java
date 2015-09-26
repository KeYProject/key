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

/**
 * Note that the RenamePackagesRefactoringTest is testing the correct moving of classes
 * indirecly as well because the ClassMoveRefactoringComputer is used internally. A renaming
 * of a package is seen as a creation of a new package, the movement of all classes from the
 * old in the new and the deletion of the old package.
 * 
 * @author Maksim Melnik, Robert Heimbach
 */
public class MoveClassRefactoringTest {

   private static final String PROJECT_NAME = "MoveClassRefactoringTest";

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static IFolder srcFolder;
   private static IProject project;
   private static IFolder oracleFolder;

   private static IJavaProject javaProject;
   final static String CLASS_NAME_MOVE = "Settings";
   final static String TESTPATH = "data\\template\\refactoringMoveTest\\moveClassTest";

   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();

      javaProject = TestUtilsUtil.createJavaProject(PROJECT_NAME);
      project = javaProject.getProject();
      srcFolder = project.getFolder(JDTUtil.getSourceFolderName());
      oracleFolder = TestUtilsUtil.createFolder(project, "oracle");

      JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(),
            JMLPreferencesHelper.getDefaultJMLProfile());
   }

   @AfterClass
   public static void deleteProject() throws CoreException {
      project.delete(true, null);
   }

   @After
   public void deleteTestPackage() throws CoreException {
      TestUtilsRefactoring.deleteAllPackagesFromFolder(srcFolder);
   }

   @Test
   public void test1SimpleMove() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveClassTest(TESTPATH + "\\test1", srcFolder, oracleFolder,
            bot, CLASS_NAME_MOVE, "test1p1", "test1p2", javaProject);

   }

   @Test
   public void test2MoveComplexPackage() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveClassTest(TESTPATH + "\\test2", srcFolder, oracleFolder,
            bot, CLASS_NAME_MOVE, "test2p1", "test2p2.complex", javaProject);

   }

   @Test
   public void test3MoveUseOps() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveClassTest(TESTPATH + "\\test3", srcFolder, oracleFolder,
            bot, CLASS_NAME_MOVE, "test3p1", "test3p2", javaProject);

   }

   @Test
   public void test4MoveComplexUseOpsBackwards() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveClassTest(TESTPATH + "\\test4", srcFolder, oracleFolder,
            bot, CLASS_NAME_MOVE, "test4p2.complex", "test4p1", javaProject);

   }

   @Test
   public void test5MoveIntoPackWithReferences() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveClassTest(TESTPATH + "\\test5", srcFolder, oracleFolder,
            bot, CLASS_NAME_MOVE, "test1p1", "mainpack", javaProject);

   }

   @Test
   public void test6NoChangeBecauseImported() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveClassTest(TESTPATH + "\\test6", srcFolder, oracleFolder,
            bot, CLASS_NAME_MOVE, "test1p1", "test1p2", javaProject);

   }

   @Test
   public void test7MoveIntoAnotherProject() throws InterruptedException, CoreException {
      // Create projects and set references
      final IProject projectSrc = TestUtilsRefactoring.createProjectWithFiles("projectSrc",
            "data\\template\\refactoringMoveTest\\moveClassTest\\test7\\projectSrc");

      final IProject projectDest = TestUtilsRefactoring.createProjectWithFiles("projectDest",
            "data\\template\\refactoringMoveTest\\moveClassTest\\test7\\projectDest");

      TestUtilsRefactoring.setProjectReferences("projectSrc", new String[] { "projectDest" },
            bot);

      // Execute Move and Check
      TestUtilsRefactoring.selectClassAndMove("projectSrc", "Other", "mainpack",
            "projectDest", "destPackage", bot);

      TestUtilsUtil.openEditor(projectSrc.getFolder(JDTUtil.getSourceFolderName())
            .getFolder("mainpack").getFile("Main" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));

      assertEquals(TestUtilsRefactoring.getOracle(projectSrc.getFolder("oracle"), "Main"),
            TestUtilsRefactoring.getContentAfterRefactoring(bot));

      projectSrc.delete(true, null);
      projectDest.delete(true, null);
   }
}
