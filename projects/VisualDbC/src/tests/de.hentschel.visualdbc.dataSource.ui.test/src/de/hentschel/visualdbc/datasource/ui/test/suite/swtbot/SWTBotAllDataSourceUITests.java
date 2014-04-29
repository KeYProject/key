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

package de.hentschel.visualdbc.datasource.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import de.hentschel.visualdbc.datasource.ui.test.testCase.swtbot.SWTBotBooleanSettingControlTest;
import de.hentschel.visualdbc.datasource.ui.test.testCase.swtbot.SWTBotDataSourceCompositeTest;
import de.hentschel.visualdbc.datasource.ui.test.testCase.swtbot.SWTBotDataSourceSettingCompositeTest;
import de.hentschel.visualdbc.datasource.ui.test.testCase.swtbot.SWTBotFileOrResourceJavaPackageSettingControlTest;
import de.hentschel.visualdbc.datasource.ui.test.testCase.swtbot.SWTBotJavaPackageSettingControlTest;
import de.hentschel.visualdbc.datasource.ui.test.testCase.swtbot.SWTBotPackageManagementSettingControlTest;
import de.hentschel.visualdbc.datasource.ui.test.testCase.swtbot.SWTBotYesNoSettingControlTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotBooleanSettingControlTest.class,
   SWTBotDataSourceCompositeTest.class,
   SWTBotDataSourceSettingCompositeTest.class,
   SWTBotFileOrResourceJavaPackageSettingControlTest.class,
   SWTBotJavaPackageSettingControlTest.class,
   SWTBotPackageManagementSettingControlTest.class,
   SWTBotYesNoSettingControlTest.class
})
public class SWTBotAllDataSourceUITests {
}