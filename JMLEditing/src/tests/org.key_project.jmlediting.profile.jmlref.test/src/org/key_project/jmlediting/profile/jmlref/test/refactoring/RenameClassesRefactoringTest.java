package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;

public class RenameClassesRefactoringTest {
    private static final String PROJECT_NAME = "JMLRefactoringRenameTestClasses";

    private static final SWTWorkbenchBot bot = new SWTWorkbenchBot();
       
    private static IFolder srcFolder;
    private static IProject project;
    private static IFolder oracleFolder;
    final String TESTPATH = "data\\template\\refactoringRenameTest\\classes";

}
