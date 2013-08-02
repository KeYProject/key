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

package org.key_project.sed.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.ui.test.testcase.swtbot.SWTBotCallStackTabTest;
import org.key_project.sed.ui.test.testcase.swtbot.SWTBotNodeTabTest;
import org.key_project.sed.ui.test.testcase.swtbot.SWTBotSourceTabTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    SWTBotCallStackTabTest.class,
    SWTBotNodeTabTest.class,
    SWTBotSourceTabTest.class
})
public class SWTBotAllSEDUITests {
}