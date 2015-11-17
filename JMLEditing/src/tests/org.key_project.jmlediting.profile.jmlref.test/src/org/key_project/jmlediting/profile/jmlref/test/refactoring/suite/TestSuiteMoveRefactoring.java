package org.key_project.jmlediting.profile.jmlref.test.refactoring.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.MoveClassRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.MoveFieldRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.MoveMethodRefactoringTest;

@RunWith(Suite.class)
@SuiteClasses({ 
      MoveClassRefactoringTest.class, 
      MoveFieldRefactoringTest.class,
      MoveMethodRefactoringTest.class })
public class TestSuiteMoveRefactoring {

}
