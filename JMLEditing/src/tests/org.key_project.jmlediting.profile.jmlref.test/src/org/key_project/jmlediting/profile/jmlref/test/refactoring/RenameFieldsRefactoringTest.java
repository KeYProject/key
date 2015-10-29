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
import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfileAE;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * The tests for the renaming of fields. See the
 * data\template\refactoringRenameTest\TestExplanation.txt for more information.
 * 
 * @author Robert Heimbach
 *
 */
public class RenameFieldsRefactoringTest {

   private static final String PROJECT_NAME = "JMLRefactoringRenameTestFields";

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private static IFolder srcFolder;
   private static IProject project;
   private static IJavaProject javaProject;
   private static IFolder oracleFolder;
   static final String TESTPATH = "data\\template\\refactoringRenameTest\\fields";

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
   public void test1SimpleAssignableClause() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test1", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aVeryLongNewName", javaProject);
   }

   @Test
   public void test2AssignableRequiresAndEnsures() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test2", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "tiny", javaProject);
   }

   @Test
   public void test3ThisQualifier() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test3", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test4TwoFilesSamePackageNoChangeInFileTwo() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test4", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test5TwoFilesSamePackageFileTwoAccessingMainClass() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test5", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test6TwoFilesOtherPackageFileTwoAccessingMainClass() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test6", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test7TwoFilesMemberAccess() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test7", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test8NoJavaChangesInOtherFile() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test8", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test9NoJavaChangesInTwoOtherFile() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test9", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test10Invariant() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test10", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test11thisQualifierMethodFieldName() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test11", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : TestClass", "newName", javaProject);
   }

   @Test
   public void test12thisQualifierMethodFieldNameNested() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test12", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : TestClass", "newName", javaProject);
   }

   @Test
   public void test13thisQualifierMethodFieldNameNestedChangedOrder() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test13", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : TestClass", "newName", javaProject);
   }

   @Test
   public void test14ManyMemberAccesses() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test14", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : TestClass", "newName", javaProject);
   }

   @Test
   public void test15MethodCallAndCast() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test15", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "newName", javaProject);
   }

   @Test
   public void test16ArrayAccessAndEquals() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test16", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : String", "newName", javaProject);
   }

   @Test
   public void test17LikeTest16WithoutParentheses() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test17", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : String", "newName", javaProject);
   }

   @Test
   public void test18ManyMemberAccessesAndMethodCalls() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test18", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "newName", javaProject);
   }

   // Test 19 and 20 can be found in {@link RenameFieldsSeveralProjectsRefactoringTest}.

   @Test
   public void test21FullyQualifiedAccessOfField() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test21", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "newName", javaProject);
   }

   @Test
   public void test22InvariantNotAboveField() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test22", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test23StaticSamePackage() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test23", srcFolder, oracleFolder,
            bot, "TestClassOther", "test", "balance : int", "aNewName", javaProject);
   }

   @Test
   public void test24JMLProfile() throws CoreException {
      JMLPreferencesHelper.setProjectJMLProfile(javaProject.getProject(),
            new JMLReferenceProfileAE());

      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test24", srcFolder, oracleFolder,
            bot, "TestClass", "test", "balance : int", "aNewName", javaProject);
   }
   
   @Test
   public void test25AccessFieldParentClass() throws CoreException {
      TestUtilsRefactoring.runFieldRenameTest(TESTPATH + "\\test25", srcFolder, oracleFolder,
            bot, "TestParent", "test", "fieldToRename : int", "aNewName", javaProject);
   }

}