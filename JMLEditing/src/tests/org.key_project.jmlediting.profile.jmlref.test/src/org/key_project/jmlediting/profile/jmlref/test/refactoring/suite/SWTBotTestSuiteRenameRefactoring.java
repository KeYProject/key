package org.key_project.jmlediting.profile.jmlref.test.refactoring.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.SWTBotRenameClassesRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.SWTBotRenameFieldsRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.SWTBotRenameFieldsSeveralProjectsRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.SWTBotRenameMethodRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.SWTBotRenamePackagesRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.SWTBotRenameParametersRefactoringTest;

@RunWith(Suite.class)
@SuiteClasses({
   SWTBotRenameFieldsRefactoringTest.class,
   SWTBotRenameFieldsSeveralProjectsRefactoringTest.class,
   SWTBotRenameParametersRefactoringTest.class,
   SWTBotRenameClassesRefactoringTest.class,
   SWTBotRenamePackagesRefactoringTest.class,
   SWTBotRenameMethodRefactoringTest.class
})

public class SWTBotTestSuiteRenameRefactoring {

}
