package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import static org.junit.Assert.assertEquals;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

/**
 * The tests for the renaming of fields when more than one project is involved. See the
 * data\template\refactoringRenameTest\TestExplanation.txt for more information.
 * 
 * @author Robert Heimbach
 *
 */
public class RenameFieldsSeveralProjectsRefactoringTest {

   private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();

   @BeforeClass
   public static void initProject() throws CoreException, InterruptedException {
      TestUtilsUtil.closeWelcomeView();
   }

   @Test
   public void test19BasicReferencing() throws InterruptedException, CoreException {
      // Create projects and set references
      final IProject referencedProject = TestUtilsRefactoring.createProjectWithFiles(
            "referencedProject",
            "data\\template\\refactoringRenameTest\\fields\\test19\\referencedProject");
      final IProject referencingProject = TestUtilsRefactoring.createProjectWithFiles(
            "referencingProject",
            "data\\template\\refactoringRenameTest\\fields\\test19\\referencingProject");
      TestUtilsRefactoring.setProjectReferences("referencingProject",
            new String[] { "referencedProject" }, bot);

      // Execute Renaming and Check
      TestUtilsRefactoring.selectElementInOutlineAndExecuteRenaming("balance : int",
            "ReferencedClass", "test",
            referencedProject.getFolder(JDTUtil.getSourceFolderName()), "aNewName", bot,
            "Rename Field");
      assertEquals(TestUtilsRefactoring.getOracle(referencedProject.getFolder("oracle"),
            "ReferencedClass"), TestUtilsRefactoring.getContentAfterRefactoring(bot));

      TestUtilsUtil.openEditor(referencingProject.getFolder(JDTUtil.getSourceFolderName())
            .getFolder("test")
            .getFile("ReferencingClass" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
      assertEquals(TestUtilsRefactoring.getOracle(referencingProject.getFolder("oracle"),
            "ReferencingClass"), TestUtilsRefactoring.getContentAfterRefactoring(bot));

      // Delete projects because of test specific java build path settings
      referencedProject.delete(true, null);
      referencingProject.delete(true, null);
   }

   @Test
   public void test20BasicPlusOwnField() throws InterruptedException, CoreException {
      // Create projects and set references
      final IProject referencedProject = TestUtilsRefactoring.createProjectWithFiles(
            "referencedProject",
            "data\\template\\refactoringRenameTest\\fields\\test20\\referencedProject");
      final IProject referencingProject = TestUtilsRefactoring.createProjectWithFiles(
            "referencingProject",
            "data\\template\\refactoringRenameTest\\fields\\test20\\referencingProject");
      TestUtilsRefactoring.setProjectReferences("referencingProject",
            new String[] { "referencedProject" }, bot);

      // Execute Renaming and Check
      TestUtilsRefactoring.selectElementInOutlineAndExecuteRenaming("balance : int",
            "ReferencedClass", "test",
            referencedProject.getFolder(JDTUtil.getSourceFolderName()), "aNewName", bot,
            "Rename Field");
      assertEquals(TestUtilsRefactoring.getOracle(referencedProject.getFolder("oracle"),
            "ReferencedClass"), TestUtilsRefactoring.getContentAfterRefactoring(bot));

      TestUtilsUtil.openEditor(referencingProject.getFolder(JDTUtil.getSourceFolderName())
            .getFolder("test")
            .getFile("ReferencingClass" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
      assertEquals(TestUtilsRefactoring.getOracle(referencingProject.getFolder("oracle"),
            "ReferencingClass"), TestUtilsRefactoring.getContentAfterRefactoring(bot));

      // Delete projects because of test specific java build path settings
      referencedProject.delete(true, null);
      referencingProject.delete(true, null);
   }
}
