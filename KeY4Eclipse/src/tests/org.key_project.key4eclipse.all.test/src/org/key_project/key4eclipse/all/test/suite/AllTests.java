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

package org.key_project.key4eclipse.all.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.core.test.suite.AllCoreTests;
import org.key_project.key4eclipse.common.ui.test.suite.AllCommonUiTests;
import org.key_project.key4eclipse.resources.test.suite.AllResourcesTests;
import org.key_project.key4eclipse.starter.core.test.suite.AllStarterCoreTests;
import org.key_project.key4eclipse.starter.ui.test.suite.AllStarterUITests;
import org.key_project.ui.test.suite.AllUITests;
import org.key_project.util.test.suite.AllUtilTests;

import de.uka.ilkd.key.proof_references.suite.AllProofReferencesTests;
import de.uka.ilkd.key.suite.AllTestGenTests;
import de.uka.ilkd.key.symbolic_execution.suite.AllSymbolicExecutionTests;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   AllUtilTests.class,
   AllCoreTests.class,
   AllProofReferencesTests.class,
   AllSymbolicExecutionTests.class,
   AllTestGenTests.class,
   AllUITests.class,
   de.uka.ilkd.key.util.removegenerics.AllTests.class,
   AllStarterCoreTests.class,
   AllCommonUiTests.class,
   AllStarterUITests.class,
   AllResourcesTests.class
})
public class AllTests {
}