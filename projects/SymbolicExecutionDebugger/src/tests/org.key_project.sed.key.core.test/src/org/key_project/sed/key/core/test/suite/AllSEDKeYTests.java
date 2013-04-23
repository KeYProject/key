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

package org.key_project.sed.key.core.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.core.test.testcase.ASTNodeByEndIndexSearcherTest;
import org.key_project.sed.key.core.test.testcase.KeYSourcePathComputerDelegateTest;
import org.key_project.sed.key.core.test.testcase.KeySEDUtilTest;
import org.key_project.sed.key.core.test.testcase.LogUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    ASTNodeByEndIndexSearcherTest.class,
    KeySEDUtilTest.class,
    KeYSourcePathComputerDelegateTest.class,
    LogUtilTest.class
})
public class AllSEDKeYTests {
}