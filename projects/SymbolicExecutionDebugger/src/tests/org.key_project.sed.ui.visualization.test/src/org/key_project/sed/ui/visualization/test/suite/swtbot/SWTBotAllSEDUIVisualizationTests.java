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

package org.key_project.sed.ui.visualization.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotGraphitiAnnotationLinksTabTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotGraphitiAnnotationsTabTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotGraphitiCallStackTabTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotGraphitiMethodReturnsTabTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotGraphitiNodeTabTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotGraphitiSourceTabTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotSaveSetAsTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotSetFileLaunchTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotSetFileSourceLookupTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotSymbolicExecutionTreeLayoutTest;
import org.key_project.sed.ui.visualization.test.testcase.swtbot.SWTBotSymbolicExecutionTreeStyleTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotGraphitiAnnotationLinksTabTest.class,
   SWTBotGraphitiAnnotationsTabTest.class,
   SWTBotGraphitiCallStackTabTest.class,
   SWTBotGraphitiMethodReturnsTabTest.class,
   SWTBotGraphitiNodeTabTest.class,
   SWTBotGraphitiSourceTabTest.class,
   SWTBotSaveSetAsTest.class,
   SWTBotSetFileLaunchTest.class,
   SWTBotSetFileSourceLookupTest.class,
   SWTBotSymbolicExecutionTreeLayoutTest.class,
   SWTBotSymbolicExecutionTreeStyleTest.class
})
public class SWTBotAllSEDUIVisualizationTests {
}