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

package de.hentschel.visualdbc.all.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.util.test.suite.swtbot.SWTBotAllUtilTests;

import de.hentschel.visualdbc.datasource.key.test.suite.swtbot.SWTBotAllKeyDataSourceTests;
import de.hentschel.visualdbc.datasource.ui.test.suite.swtbot.SWTBotAllDataSourceUITests;
import de.hentschel.visualdbc.dbcmodel.diagram.custom.test.suite.swtbot.SWTBotAllDiagramCustomTests;
import de.hentschel.visualdbc.example.test.suite.swtbot.SWTBotAllExampleTests;
import de.hentschel.visualdbc.generation.ui.test.suite.swtbot.SWTBotAllGenerationUiTests;
import de.hentschel.visualdbc.interactive.proving.ui.test.suite.swtbot.SWTBotAllInteractiveProvingUiTests;
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
   SWTBotAllUtilTests.class,
   SWTBotAllDataSourceUITests.class,
   SWTBotAllGenerationUiTests.class,
   SWTBotAllDiagramCustomTests.class,
   SWTBotAllKeyDataSourceTests.class,
   SWTBotAllInteractiveProvingUiTests.class,
   SWTBotAllExampleTests.class
})
public class SWTBotAllVisualDbCTests {
}