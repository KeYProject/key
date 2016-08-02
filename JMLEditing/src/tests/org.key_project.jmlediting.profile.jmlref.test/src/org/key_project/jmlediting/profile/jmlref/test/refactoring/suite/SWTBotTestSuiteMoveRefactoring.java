package org.key_project.jmlediting.profile.jmlref.test.refactoring.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.SWTBotMoveClassRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.SWTBotMoveFieldRefactoringTest;
import org.key_project.jmlediting.profile.jmlref.test.refactoring.SWTBotMoveMethodRefactoringTest;

@RunWith(Suite.class)
@SuiteClasses({ 
      SWTBotMoveClassRefactoringTest.class, 
      SWTBotMoveFieldRefactoringTest.class,
      SWTBotMoveMethodRefactoringTest.class })
public class SWTBotTestSuiteMoveRefactoring {

}
