/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.sed.key.core.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotContractTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYDebugTargetProofFileTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYDebugTargetTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYLaunchConfigurationDelegateTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYModelThreadSaveChildAccessTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYSourceLookupParticipantTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotLaunchDefaultPreferencesTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotMaximalNumberOfSetNodesPerBranchOnRunTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotStepOverTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotStepReturnTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotContractTest.class,
   SWTBotKeYDebugTargetProofFileTest.class,
   SWTBotKeYDebugTargetTest.class,
   SWTBotKeYLaunchConfigurationDelegateTest.class,
   SWTBotKeYModelThreadSaveChildAccessTest.class,
   SWTBotKeYSourceLookupParticipantTest.class,
   SWTBotLaunchDefaultPreferencesTest.class,
   SWTBotMaximalNumberOfSetNodesPerBranchOnRunTest.class,
   SWTBotStepOverTest.class,
   SWTBotStepReturnTest.class
})
public class SWTBotAllSEDKeYTests {
}