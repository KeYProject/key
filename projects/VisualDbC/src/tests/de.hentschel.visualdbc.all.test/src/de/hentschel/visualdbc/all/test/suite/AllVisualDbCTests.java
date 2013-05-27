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

package de.hentschel.visualdbc.all.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.util.test.suite.AllUtilTests;

import de.hentschel.visualdbc.datasource.key.test.suite.AllKeyDataSourceTests;
import de.hentschel.visualdbc.datasource.test.suite.AllDataSourceTests;
import de.hentschel.visualdbc.datasource.ui.test.suite.AllDataSourceUITests;
import de.hentschel.visualdbc.dbcmodel.diagram.custom.test.suite.AllDiagramCustomTests;
import de.hentschel.visualdbc.example.test.suite.AllExampleTests;
import de.hentschel.visualdbc.generation.test.suite.AllGenerationTests;
import de.hentschel.visualdbc.generation.ui.test.suite.AllGenerationUiTests;
import de.hentschel.visualdbc.interactive.proving.ui.test.suite.AllInteractiveProvingUiTests;
import de.hentschel.visualdbc.key.ui.test.suite.AllKeYUiTests;

/**
 * <p>
 * Run all contained JUnit 4 test cases.
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
   AllUtilTests.class,
   AllDataSourceTests.class,
   AllDataSourceUITests.class,
   AllGenerationTests.class,
   AllGenerationUiTests.class,
   AllKeyDataSourceTests.class,
   AllDiagramCustomTests.class,
   AllInteractiveProvingUiTests.class,
   AllExampleTests.class,
   AllKeYUiTests.class
})
   // TODO: Add unit 3 suite DbcModelAllTests
public class AllVisualDbCTests {
}