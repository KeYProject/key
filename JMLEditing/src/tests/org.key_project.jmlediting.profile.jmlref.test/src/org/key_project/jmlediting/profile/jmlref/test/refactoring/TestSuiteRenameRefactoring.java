package org.key_project.jmlediting.profile.jmlref.test.refactoring;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({
    RenameFieldsRefactoringTest.class,
    RenameFieldsSeveralProjectsRefactoringTest.class,
    RenameParametersRefactoringTest.class,
    RenameClassesRefactoringTest.class
})

public class TestSuiteRenameRefactoring {

}
