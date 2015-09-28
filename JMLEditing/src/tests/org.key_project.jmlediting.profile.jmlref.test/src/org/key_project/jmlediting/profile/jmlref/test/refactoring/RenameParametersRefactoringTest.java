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

/**
 * The tests for the renaming of parameters. See the
 * data\template\refactoringRenameTest\TestExplanation.txt for more information.
 * 
 * @author Robert Heimbach
 *
 */
public class RenameParametersRefactoringTest {
   private static final String PROJECT_NAME = "JMLRefactoringRenameTestParameters";

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static IFolder srcFolder;
   private static IProject project;
   private static IFolder oracleFolder;
   static final String TESTPATH = "data\\template\\refactoringRenameTest\\parameters";

   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();

      final IJavaProject javaProject = TestUtilsUtil.createJavaProject(PROJECT_NAME);
      project = javaProject.getProject();
      srcFolder = project.getFolder(JDTUtil.getSourceFolderName());
      oracleFolder = TestUtilsUtil.createFolder(project, "oracle");

      JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(),
            JMLPreferencesHelper.getDefaultJMLProfile());
   }

   @After
   public void deleteTestPackage() throws CoreException {
      srcFolder.getFolder("test").delete(true, null);
   }

   @Test
   public void test1OneParameter() throws CoreException {
      TestUtilsRefactoring.runParameterRenameTest(TESTPATH + "\\test1", srcFolder,
            oracleFolder, bot, "TestClass", "test", "setBalance(int) : void", "aNewName", 7);
   }

   @Test
   public void test2TwoParametersFirst() throws CoreException {
      TestUtilsRefactoring.runParameterRenameTest(TESTPATH + "\\test2", srcFolder,
            oracleFolder, bot, "TestClass", "test", "setBalance(int, boolean) : void",
            "aNewName", 7);
   }

   @Test
   public void test3TwoParametersSecond() throws CoreException {
      TestUtilsRefactoring.runParameterRenameTest(TESTPATH + "\\test3", srcFolder,
            oracleFolder, bot, "TestClass", "test", "setBalance(boolean, int) : void",
            "aNewName", 26);
   }

   @Test
   public void test4FieldAndOtherMethodUsingSameName() throws CoreException {
      TestUtilsRefactoring.runParameterRenameTest(TESTPATH + "\\test4", srcFolder,
            oracleFolder, bot, "TestClass", "test", "setBalance(boolean, int) : void",
            "aNewName", 26);
   }

   @Test
   public void test5RenameLocalVariableNoParameter() throws CoreException {
      TestUtilsRefactoring.runParameterRenameTest(TESTPATH + "\\test5", srcFolder,
            oracleFolder, bot, "TestClass", "test", "setBalance(boolean) : void", "aNewName",
            26);
   }
}
