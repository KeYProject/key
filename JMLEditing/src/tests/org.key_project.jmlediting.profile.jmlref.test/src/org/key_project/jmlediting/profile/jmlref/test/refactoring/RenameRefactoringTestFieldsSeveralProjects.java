package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import static org.junit.Assert.assertEquals;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.util.jdt.JDTUtil;
import org.key_project.util.test.util.TestUtilsUtil;

public class RenameRefactoringTestFieldsSeveralProjects {

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    
    @BeforeClass
    public static void initProject() throws CoreException, InterruptedException {
        TestUtilsUtil.closeWelcomeView();    
    }
    
    @Test
    public void test19BasicReferencing() throws InterruptedException, CoreException {
        // Create projects and set references
       final IProject referencedProject = RefactoringTestUtil.createProjectWithFiles("referencedProject", "data\\template\\refactoringRenameTest\\fields\\test19\\referencedProject");
       final IProject referencingProject = RefactoringTestUtil.createProjectWithFiles("referencingProject", "data\\template\\refactoringRenameTest\\fields\\test19\\referencingProject");
       RefactoringTestUtil.setProjectReferences("referencingProject", new String[]{"referencedProject"}, bot);
       
       // Execute Renaming and Check
       TestUtilsUtil.openEditor(referencedProject.getFolder(JDTUtil.getSourceFolderName()).getFolder("test").getFile("ReferencedClass" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       RefactoringTestUtil.selectFieldAndExecuteRenaming("balance : int", "ReferencedClass", "test", referencedProject.getFolder(JDTUtil.getSourceFolderName()), "aNewName", bot);
       assertEquals(RefactoringTestUtil.getOracle(referencedProject.getFolder("oracle"), "ReferencedClass"),RefactoringTestUtil.getContentAfterRefactoring(bot));
       
       TestUtilsUtil.openEditor(referencingProject.getFolder(JDTUtil.getSourceFolderName()).getFolder("test").getFile("ReferencingClass" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       assertEquals(RefactoringTestUtil.getOracle(referencingProject.getFolder("oracle"), "ReferencingClass"),RefactoringTestUtil.getContentAfterRefactoring(bot));
       
       // Delete projects because of test specific java build path settings
       referencedProject.delete(true, null);
       referencingProject.delete(true, null);
   }
   
    @Test
    public void test20BasicPlusOwnField() throws InterruptedException, CoreException {
        // Create projects and set references
       final IProject referencedProject = RefactoringTestUtil.createProjectWithFiles("referencedProject", "data\\template\\refactoringRenameTest\\fields\\test20\\referencedProject");
       final IProject referencingProject = RefactoringTestUtil.createProjectWithFiles("referencingProject", "data\\template\\refactoringRenameTest\\fields\\test20\\referencingProject");
       RefactoringTestUtil.setProjectReferences("referencingProject", new String[]{"referencedProject"}, bot);
       
       // Execute Renaming and Check
       TestUtilsUtil.openEditor(referencedProject.getFolder(JDTUtil.getSourceFolderName()).getFolder("test").getFile("ReferencedClass" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       RefactoringTestUtil.selectFieldAndExecuteRenaming("balance : int", "ReferencedClass", "test", referencedProject.getFolder(JDTUtil.getSourceFolderName()), "aNewName", bot);
       assertEquals(RefactoringTestUtil.getOracle(referencedProject.getFolder("oracle"), "ReferencedClass"),RefactoringTestUtil.getContentAfterRefactoring(bot));
       
       TestUtilsUtil.openEditor(referencingProject.getFolder(JDTUtil.getSourceFolderName()).getFolder("test").getFile("ReferencingClass" + JDTUtil.JAVA_FILE_EXTENSION_WITH_DOT));
       assertEquals(RefactoringTestUtil.getOracle(referencingProject.getFolder("oracle"), "ReferencingClass"),RefactoringTestUtil.getContentAfterRefactoring(bot));
       
       // Delete projects because of test specific java build path settings
       referencedProject.delete(true, null);
       referencingProject.delete(true, null);
    }
}
