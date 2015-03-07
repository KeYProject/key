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

package org.key_project.sed.key.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotAddKeYWatchpointTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotCustomizationTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotGraphitiCustomizationTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotGraphitiKeYTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotGraphitiLoopInvariantTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotGraphitiMainTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotGraphitiPostconditionTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotGraphitiPreconditionTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotKeYSourceCodeLookupTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotKeYTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotLoopInvariantTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotMainTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotOpenProofTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotPostconditionTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotPreconditionTabTest;
import org.key_project.sed.key.ui.test.testcase.swtbot.SWTBotSideProofsViewTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotCustomizationTabTest.class,
   SWTBotGraphitiCustomizationTabTest.class,
   SWTBotGraphitiKeYTabTest.class,
   SWTBotGraphitiLoopInvariantTabTest.class,
   SWTBotGraphitiMainTabTest.class,
   SWTBotGraphitiPostconditionTabTest.class,
   SWTBotGraphitiPreconditionTabTest.class,
   SWTBotKeYSourceCodeLookupTest.class,
   SWTBotKeYTabTest.class,
   SWTBotLoopInvariantTabTest.class,
   SWTBotMainTabTest.class,
   SWTBotAddKeYWatchpointTest.class,
   SWTBotOpenProofTest.class,
   SWTBotPostconditionTabTest.class,
   SWTBotPreconditionTabTest.class,
   SWTBotSideProofsViewTest.class
})
public class SWTBotAllSEDKeYUITests {
}