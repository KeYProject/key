package org.key_project.jmlediting.profile.jmlref.test.refactoring;

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

public class MoveMethodRefactoringTest {

   private static final String PROJECT_NAME = "MoveMethodRefactoringTest";

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static IFolder srcFolder;
   private static IProject project;
   private static IFolder oracleFolder;

   private static IJavaProject javaProject;
   static final String TESTPATH = "data\\template\\refactoringMoveTest\\moveMethodTest";
   static final String CLASS_NAME_MOVE_FROM = "Settings";
   static final String CLASS_NAME_MOVE_TO = "Params";
   static final String METH_TO_MOVE = "go";

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

   @After
   public void deleteTestPackage() throws CoreException {
      TestUtilsRefactoring.deleteAllPackagesFromFolder(srcFolder);
   }

   @AfterClass
   public static void deleteProject() throws CoreException {
      project.delete(true, null);
   }

   @Test
   public void test1SimpleMove() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveOutlineElementTest(TESTPATH + "\\test1", srcFolder,
            oracleFolder, bot, CLASS_NAME_MOVE_FROM, "test1p1", METH_TO_MOVE + "() : void",
            CLASS_NAME_MOVE_TO, "test1p2", javaProject);
   }

   @Test
   public void test2MoveComplexPackage() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveOutlineElementTest(TESTPATH + "\\test2", srcFolder,
            oracleFolder, bot, CLASS_NAME_MOVE_FROM, "test2p1", METH_TO_MOVE + "() : void",
            CLASS_NAME_MOVE_TO, "test2p2.complex", javaProject);

   }

   @Test
   public void test3MoveUseOps() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveOutlineElementTest(TESTPATH + "\\test3", srcFolder,
            oracleFolder, bot, CLASS_NAME_MOVE_FROM, "test3p1", METH_TO_MOVE + "() : void",
            CLASS_NAME_MOVE_TO, "test3p2", javaProject);

   }

   @Test
   public void test4MoveComplexUseOpsBackwards() throws InterruptedException, CoreException {

      TestUtilsRefactoring.runMoveOutlineElementTest(TESTPATH + "\\test4", srcFolder,
            oracleFolder, bot, CLASS_NAME_MOVE_TO, "test4p2\\complex", METH_TO_MOVE
                  + "() : void", CLASS_NAME_MOVE_FROM, "test4p1", javaProject);

   }
}
