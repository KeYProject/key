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

package org.key_project.sed.key.core.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotAddBreakpointsPostResume;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotAddBreakpointsPostTarget;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeAccessModification;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeCaughtUncaughtSubclasses;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeConditonWithErrorCancel;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeConditonWithErrorOKThenCancel;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeConditonWithErrorOKThenOKWithChange;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeConditonWithErrorOKThenOKWithoutChange;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeConditonWithoutError;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeEnabled;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeEntryExit;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotChangeHitCount;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotContractTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotHotCodeReplaceContinueTestCase;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotHotCodeReplaceDisconnectTestCase;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotHotCodeReplacePreferenceTestCase;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotHotCodeReplaceTerminateTestCase;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotInitialAnnotationLinkTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYDebugTargetProofFileTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYDebugTargetTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYLaunchConfigurationDelegateTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYModelThreadSaveChildAccessTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotKeYSourceLookupParticipantTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotLaunchDefaultPreferencesTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotMaximalNumberOfSetNodesPerBranchOnRunTest;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotRemoveExceptionBreakpoint;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotRemoveLineBreakpoint;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotRemoveMethodBreakpoint;
import org.key_project.sed.key.core.test.testcase.swtbot.SWTBotRemoveWatchpoint;
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
   SWTBotStepReturnTest.class,
   SWTBotAddBreakpointsPostResume.class,
   SWTBotAddBreakpointsPostTarget.class,
   SWTBotChangeAccessModification.class,
   SWTBotChangeCaughtUncaughtSubclasses.class,
   SWTBotChangeConditonWithErrorCancel.class,
   SWTBotChangeConditonWithErrorOKThenCancel.class,
   SWTBotChangeConditonWithErrorOKThenOKWithChange.class,
   SWTBotChangeConditonWithErrorOKThenOKWithoutChange.class,
   SWTBotChangeConditonWithoutError.class,
   SWTBotChangeEnabled.class,
   SWTBotChangeEntryExit.class,
   SWTBotChangeHitCount.class,
   SWTBotHotCodeReplaceContinueTestCase.class,
   SWTBotHotCodeReplaceDisconnectTestCase.class,
   SWTBotHotCodeReplacePreferenceTestCase.class,
   SWTBotHotCodeReplaceTerminateTestCase.class,
   SWTBotInitialAnnotationLinkTest.class,
   SWTBotRemoveExceptionBreakpoint.class,
   SWTBotRemoveLineBreakpoint.class,
   SWTBotRemoveMethodBreakpoint.class,
   SWTBotRemoveWatchpoint.class
})
public class SWTBotAllSEDKeYTests {
}