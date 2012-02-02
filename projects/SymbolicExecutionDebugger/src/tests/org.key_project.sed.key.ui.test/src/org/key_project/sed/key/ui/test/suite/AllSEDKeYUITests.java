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

package org.key_project.sed.key.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.ui.test.testcase.AllOperationsSearchEngineTest;
import org.key_project.sed.key.ui.test.testcase.AllTypesSearchEngineTest;
import org.key_project.sed.key.ui.test.testcase.KeYSEDImagesTest;
import org.key_project.sed.key.ui.test.testcase.LogUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    AllOperationsSearchEngineTest.class,
    AllTypesSearchEngineTest.class,
    KeYSEDImagesTest.class,
    LogUtilTest.class
})
public class AllSEDKeYUITests {
}
