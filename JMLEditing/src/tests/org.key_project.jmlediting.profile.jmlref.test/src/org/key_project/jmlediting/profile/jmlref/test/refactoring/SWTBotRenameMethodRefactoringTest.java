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
 * The tests for the renaming of methods. See the
 * data\template\refactoringRenameTest\TestExplanation.txt for more information.
 * 
 * @author Robert Heimbach
 *
 */
public class SWTBotRenameMethodRefactoringTest {

   private static final String PROJECT_NAME = "JMLRefactoringRenameTestMethods";

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static IFolder srcFolder;
   private static IProject project;
   private static IJavaProject javaProject;
   private static IFolder oracleFolder;
   static final String TESTPATH = "data\\template\\refactoringRenameTest\\methods";

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

   @Test
   public void test1SameClassNoOther() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test1", srcFolder, oracleFolder,
            bot, "TestClass", "test", "getBalance() : int", "newMethodName", javaProject);
   }

   @Test
   public void test2SameClassOtherMethodWithSameNamePresent() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test2", srcFolder, oracleFolder,
            bot, "TestClass", "test", "getBalance() : int", "newMethodName", javaProject);
   }

   @Test
   public void test3SameClassOtherMethodWithSameNamePresentCheck() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test3", srcFolder, oracleFolder,
            bot, "TestClass", "test", "getBalance(boolean) : int", "newMethodName",
            javaProject);
   }

   @Test
   public void test4SameClassOtherTwoMethodsWithSameName() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test4", srcFolder, oracleFolder,
            bot, "TestClass", "test", "getBalance(boolean) : int", "newMethodName",
            javaProject);
   }

   @Test
   public void test5TwoClassesSamePackage() throws Exception {
      TestUtilsRefactoring
            .runMethodRenameTest(TESTPATH + "\\test5", srcFolder, oracleFolder, bot,
                  "TestClassOther", "test", "getBalance() : int", "newMethodName",
                  javaProject);
   }

   @Test
   public void test6TwoClassesSamePackageTrueNegativeCheck() throws Exception {
      TestUtilsRefactoring
            .runMethodRenameTest(TESTPATH + "\\test6", srcFolder, oracleFolder, bot,
                  "TestClassOther", "test", "getBalance() : int", "newMethodName",
                  javaProject);
   }

   @Test
   public void test7TwoClassesDifferentPackage() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test7", srcFolder, oracleFolder,
            bot, "TestClassOther", "otherPackage", "getBalance() : int", "newMethodName",
            javaProject);
   }

   @Test
   public void test8NestedCallsMethodFromClass() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test8", srcFolder, oracleFolder,
            bot, "TestClass", "test", "getBalance() : int", "newMethodName", javaProject);
   }

   @Test
   public void test9NestedCallsStringValueOf() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test9", srcFolder, oracleFolder,
            bot, "TestClass", "test", "getBalance() : int", "newMethodName", javaProject);
   }

   @Test
   public void test10SuccessiveMethodCalls() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test10", srcFolder,
            oracleFolder, bot, "TestClass", "test", "getBalance() : int", "newMethodName",
            javaProject);
   }

   @Test
   public void test11SuccessiveMethodCallsAsArgument() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test11", srcFolder,
            oracleFolder, bot, "TestClass", "test", "getBalance() : int", "newMethodName",
            javaProject);
   }

   @Test
   public void test12ThreeSuccessiveMethodCalls() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test12", srcFolder,
            oracleFolder, bot, "TestClass", "test", "getBalance() : String", "newMethodName",
            javaProject);
   }

   @Test
   public void test13SuccessiveMethodCallsWithExtraParenthesis() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test13", srcFolder,
            oracleFolder, bot, "TestClass", "test", "getBalance() : int", "newMethodName",
            javaProject);
   }

   @Test
   public void test14SuccessiveMethodCallsWithArguments() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test14", srcFolder,
            oracleFolder, bot, "TestClass", "test", "getBalance() : int", "newMethodName",
            javaProject);
   }

   @Test
   public void test15TwoClassesSamePackageStatic() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test15", srcFolder,
            oracleFolder, bot, "TestClassOther", "test", "getBalance() : int",
            "newMethodName", javaProject);
   }

   @Test
   public void test16TwoClassesDifferentPackageStatic() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test16", srcFolder,
            oracleFolder, bot, "TestClassOther", "otherPackage", "getBalance() : int",
            "newMethodName", javaProject);
   }
   
   @Test
   public void test17MethodOverride() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test17", srcFolder,
            oracleFolder, bot, "TestParent", "test", "returnAnInteger() : int",
            "aNewMethodName", javaProject);
   }
   
   @Test
   public void test18Cast() throws Exception {
      TestUtilsRefactoring.runMethodRenameTest(TESTPATH + "\\test18", srcFolder,
            oracleFolder, bot, "TestParent", "test", "returnAnInteger() : int",
            "newMethodName", javaProject);
   }
}
