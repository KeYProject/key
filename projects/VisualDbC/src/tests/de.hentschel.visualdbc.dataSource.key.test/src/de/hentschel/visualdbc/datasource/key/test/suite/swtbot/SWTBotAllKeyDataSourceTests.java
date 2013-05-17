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

package de.hentschel.visualdbc.datasource.key.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import de.hentschel.visualdbc.datasource.key.test.testCase.swtbot.SWTBotKeyAxiomContractTest;
import de.hentschel.visualdbc.datasource.key.test.testCase.swtbot.SWTBotKeyInteractiveMainTest;
import de.hentschel.visualdbc.datasource.key.test.testCase.swtbot.SWTBotKeyOperationContractTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotKeyAxiomContractTest.class,
   SWTBotKeyInteractiveMainTest.class,
   SWTBotKeyOperationContractTest.class
})
public class SWTBotAllKeyDataSourceTests {
}