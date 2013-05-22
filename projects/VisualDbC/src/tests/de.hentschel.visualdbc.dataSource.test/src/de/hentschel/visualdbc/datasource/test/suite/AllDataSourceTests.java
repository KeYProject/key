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

package de.hentschel.visualdbc.datasource.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import de.hentschel.visualdbc.datasource.test.testCase.AbstractDSConnectionTest;
import de.hentschel.visualdbc.datasource.test.testCase.AbstractDSContainerTest;
import de.hentschel.visualdbc.datasource.test.testCase.AbstractDSDriverTest;
import de.hentschel.visualdbc.datasource.test.testCase.AbstractDSOperationTest;
import de.hentschel.visualdbc.datasource.test.testCase.AbstractDSProvableTest;
import de.hentschel.visualdbc.datasource.test.testCase.AbstractDSTypeTest;
import de.hentschel.visualdbc.datasource.test.testCase.DataSourceIteratorTest;
import de.hentschel.visualdbc.datasource.test.testCase.DriverUtilTest;
import de.hentschel.visualdbc.datasource.test.testCase.LogUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   AbstractDSConnectionTest.class,
   AbstractDSContainerTest.class,
   AbstractDSDriverTest.class,
   AbstractDSOperationTest.class,
   AbstractDSProvableTest.class,
   AbstractDSTypeTest.class,
   DataSourceIteratorTest.class,
   DriverUtilTest.class,
   LogUtilTest.class
})
public class AllDataSourceTests {
}