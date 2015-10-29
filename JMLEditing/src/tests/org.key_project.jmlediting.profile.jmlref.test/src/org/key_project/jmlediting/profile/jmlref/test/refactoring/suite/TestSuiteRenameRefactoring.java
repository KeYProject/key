package org.key_project.jmlediting.profile.jmlref.test.refactoring.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.RenameClassesRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.RenameFieldsRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.RenameFieldsSeveralProjectsRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.RenameMethodRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.RenamePackagesRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.RenameParametersRefactoringTest;

@RunWith(Suite.class)
@SuiteClasses({
   RenameFieldsRefactoringTest.class,
   RenameFieldsSeveralProjectsRefactoringTest.class,
   RenameParametersRefactoringTest.class,
   RenameClassesRefactoringTest.class,
   RenamePackagesRefactoringTest.class,
   RenameMethodRefactoringTest.class
})

public class TestSuiteRenameRefactoring {

}
