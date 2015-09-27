package org.key_project.jmlediting.ui.test.outline;


import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

@RunWith(Suite.class)
@SuiteClasses({
   // parser
   SWTBotJMLOutlineView.class,
   SWTBotJMLOutlineSpecPure.class,
   SWTBotJMLOutlineUpdate.class
})

public class JMLOutlineAllTestSuit {

}
