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

package de.hentschel.visualdbc.interactive.proving.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.DbcModelUtilTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.DefaultDSFinderFactoryTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.DefaultDSFinderTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.DefaultDbcFinderFactoryTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.DefaultDbcFinderTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.FinderUtilTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.InteractiveConnectionUtilTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.InteractiveProvingPreferencesInitializerTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.InteractiveProvingPreferencesTest;
import de.hentschel.visualdbc.interactive.proving.ui.test.testCase.LogUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   DbcModelUtilTest.class,
   DefaultDbcFinderFactoryTest.class,
   DefaultDbcFinderTest.class,
   DefaultDSFinderFactoryTest.class,
   DefaultDSFinderTest.class,
   FinderUtilTest.class,
   InteractiveProvingPreferencesInitializerTest.class,
   InteractiveProvingPreferencesTest.class,
   InteractiveConnectionUtilTest.class,
   LogUtilTest.class
})
public class AllInteractiveProvingUiTests {
}