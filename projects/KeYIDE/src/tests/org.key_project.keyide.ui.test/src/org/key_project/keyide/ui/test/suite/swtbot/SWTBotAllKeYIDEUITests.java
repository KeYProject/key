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

package org.key_project.keyide.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.keyide.ui.test.testcase.swtbot.SWTBotAutoModeHandlerTest;
import org.key_project.keyide.ui.test.testcase.swtbot.SWTBotKeYIDEPreferencePageTest;
import org.key_project.keyide.ui.test.testcase.swtbot.SWTBotManualRuleApplicationTest;
import org.key_project.keyide.ui.test.testcase.swtbot.SWTBotStartProofHandlerTest;

/**
 * <p>
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * </p>
 * <p>
 * Requires the following JVM settings: -Xms128m -Xmx1024m -XX:MaxPermSize=256m
 * </p>
 * <p>
 * If you got timeout exceptions increase the waiting time with the following
 * additional JVM parameter: -Dorg.eclipse.swtbot.search.timeout=10000
 * </p>
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotAutoModeHandlerTest.class,
   SWTBotKeYIDEPreferencePageTest.class,
   SWTBotManualRuleApplicationTest.class,
   SWTBotStartProofHandlerTest.class
})
public class SWTBotAllKeYIDEUITests {
}
