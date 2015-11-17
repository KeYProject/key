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

package org.key_project.sed.core.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.core.test.testcase.LogUtilTest;
import org.key_project.sed.core.test.testcase.SEBreadthFirstIteratorTest;
import org.key_project.sed.core.test.testcase.SEPostorderIteratorTest;
import org.key_project.sed.core.test.testcase.SEPreferenceUtilInitializerTest;
import org.key_project.sed.core.test.testcase.SEPreferenceUtilTest;
import org.key_project.sed.core.test.testcase.SEPreorderIteratorTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   LogUtilTest.class,
   SEBreadthFirstIteratorTest.class,
   SEPostorderIteratorTest.class,
   SEPreferenceUtilInitializerTest.class,
   SEPreferenceUtilTest.class,
   SEPreorderIteratorTest.class
})
public class AllSEDCoreTests {
}