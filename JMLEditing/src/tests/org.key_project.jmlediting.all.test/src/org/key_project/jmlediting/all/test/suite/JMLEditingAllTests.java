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

package org.key_project.jmlediting.all.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.jmlediting.core.test.suite.JMLEditingAllCoreTestSuite;
import org.key_project.jmlediting.profile.jmlref.test.suite.JMLEditingAllJMLRefTestSuite;
import org.key_project.jmlediting.profile.key.test.suite.JMLEditingAllKeYProfileTestSuite;
import org.key_project.util.test.suite.AllUtilTests;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   AllUtilTests.class,
   JMLEditingAllCoreTestSuite.class,
   JMLEditingAllJMLRefTestSuite.class,
   JMLEditingAllKeYProfileTestSuite.class
})
public class JMLEditingAllTests {
}