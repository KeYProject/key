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
 * The tests for the renaming of classes. See the
 * data\template\refactoringRenameTest\TestExplanation.txt for more information.
 * 
 * @author Robert Heimbach
 *
 */
public class RenameClassesRefactoringTest {
   private static final String PROJECT_NAME = "JMLRefactoringRenameTestClasses";

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static IFolder srcFolder;
   private static IProject project;
   private static IFolder oracleFolder;
   private static IJavaProject javaProject;
   final static String TESTPATH = "data\\template\\refactoringRenameTest\\classes";

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
   public void test1JavaAndJMLOneClass() throws CoreException {
      TestUtilsRefactoring.runClassRenameTestBasic(TESTPATH + "\\test1", srcFolder,
            oracleFolder, bot, "TestClass", "test", "NewClassName", javaProject);
   }

   @Test
   public void test2NoJavaOneClass() throws CoreException {
      TestUtilsRefactoring.runClassRenameTestBasic(TESTPATH + "\\test2", srcFolder,
            oracleFolder, bot, "TestClass", "test", "NewClassName", javaProject);
   }

   @Test
   public void test3TwoClassesSamePackage() throws CoreException {
      TestUtilsRefactoring.runClassRenameTestBasic(TESTPATH + "\\test3", srcFolder,
            oracleFolder, bot, "TestClass", "test", "NewClassName", javaProject);
   }

   @Test
   public void test4TwoClassesSamePackageNoJavaChanges() throws CoreException {
      TestUtilsRefactoring.runClassRenameTestBasic(TESTPATH + "\\test4", srcFolder,
            oracleFolder, bot, "TestClass", "test", "NewClassName", javaProject);
   }

   @Test
   public void test5TwoClassesDifferentPackage() throws CoreException {
      TestUtilsRefactoring.runClassRenameTestBasic(TESTPATH + "\\test5", srcFolder,
            oracleFolder, bot, "TestClass", "test", "NewClassName", javaProject);
   }

   @Test
   public void test6FullyQualifiedClassAccess() throws CoreException {
      TestUtilsRefactoring.runClassRenameTestBasic(TESTPATH + "\\test6", srcFolder,
            oracleFolder, bot, "TestClass", "test", "NewClassName", javaProject);
   }

   @Test
   public void test7NoChangesOtherStringClassUsed() throws CoreException {
      TestUtilsRefactoring.runClassRenameTestBasic(TESTPATH + "\\test7", srcFolder,
            oracleFolder, bot, "Integer", "test", "NewClassName", javaProject);
   }

   @Test
   public void test8ReferencedInCastExpression() throws CoreException {
      TestUtilsRefactoring.runClassRenameTestBasic(TESTPATH + "\\test8", srcFolder,
            oracleFolder, bot, "TestClass", "test", "NewClassName", javaProject);
   }
}
