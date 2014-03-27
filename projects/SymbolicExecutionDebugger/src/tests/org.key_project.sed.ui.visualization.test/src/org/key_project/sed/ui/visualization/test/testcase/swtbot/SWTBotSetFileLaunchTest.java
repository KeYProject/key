package org.key_project.sed.ui.visualization.test.testcase.swtbot;

import org.junit.Test;
import org.key_project.sed.ui.visualization.launch.SETFileLaunchConfigurationDelegate;
import org.key_project.sed.ui.visualization.launch.SETFileLaunchShortcut;

/**
 * SWTBot tests to launch SET files. This involves in particular
 * {@link SETFileLaunchConfigurationDelegate} and
 * {@link SETFileLaunchShortcut}.
 * @author Martin Hentschel
 */
public class SWTBotSetFileLaunchTest extends AbstractSWTBotSetFileTest {
   /**
    * Launches "data/Number/src/Number.set".
    */
   @Test
   public void testSetFile() throws Exception {
      doSetFileTest("SWTBotSetFileLaunchTest_testSetFile", 
                    "data/Number/src", 
                    "Number.set",
                    null);
   }
}
