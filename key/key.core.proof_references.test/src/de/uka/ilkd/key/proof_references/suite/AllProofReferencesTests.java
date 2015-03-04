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
package de.uka.ilkd.key.proof_references.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   de.uka.ilkd.key.proof_references.testcase.TestKeYTypeUtil.class,
   de.uka.ilkd.key.proof_references.testcase.TestProofReferenceUtil.class,
   de.uka.ilkd.key.proof_references.testcase.analyst.TestProgramVariableReferencesAnalyst.class,
   de.uka.ilkd.key.proof_references.testcase.analyst.TestClassAxiomAndInvariantProofReferencesAnalyst.class,
   de.uka.ilkd.key.proof_references.testcase.analyst.TestContractProofReferencesAnalyst.class,
   de.uka.ilkd.key.proof_references.testcase.analyst.TestMethodBodyExpandProofReferencesAnalyst.class,
   de.uka.ilkd.key.proof_references.testcase.analyst.TestMethodCallProofReferencesAnalyst.class
})
public class AllProofReferencesTests {
}