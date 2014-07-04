/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

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
    * Launches "data/Number/test/Number.set".
    */
   @Test
   public void testSetFile() throws Exception {
      doSetFileTest("SWTBotSetFileLaunchTest_testSetFile", 
                    "data/Number/test", 
                    "Number.set",
                    null);
   }
}