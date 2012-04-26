/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.interactive.proving.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.swtbot.SWTBotInteractiveProofingPreferencePageTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.swtbot.SWTBotOpenProofCommandTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotInteractiveProofingPreferencePageTest.class,
   SWTBotOpenProofCommandTest.class
})
public class SWTBotAllInteractiveProvingUiTests {
}
