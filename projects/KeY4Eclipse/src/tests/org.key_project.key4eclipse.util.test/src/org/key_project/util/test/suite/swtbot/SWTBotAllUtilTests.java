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

package org.key_project.util.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.util.test.testcase.swtbot.SWTBotAbstractEditorInViewViewTest;
import org.key_project.util.test.testcase.swtbot.SWTBotContentWizardNewFileCreationPageTest;
import org.key_project.util.test.testcase.swtbot.SWTBotLoggerTest;
import org.key_project.util.test.testcase.swtbot.SWTBotTableSelectionDialogTest;
import org.key_project.util.test.testcase.swtbot.SWTBotWorkbenchUtilTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    SWTBotAbstractEditorInViewViewTest.class,
    SWTBotContentWizardNewFileCreationPageTest.class,
    SWTBotLoggerTest.class,
    SWTBotTableSelectionDialogTest.class,
    SWTBotWorkbenchUtilTest.class
})
public class SWTBotAllUtilTests {
}