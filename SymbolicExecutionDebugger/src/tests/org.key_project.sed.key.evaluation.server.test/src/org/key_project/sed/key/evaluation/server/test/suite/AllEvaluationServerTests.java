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

package org.key_project.sed.key.evaluation.server.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.sed.key.evaluation.server.test.testcase.AbstractRandomCompletionTest;
import org.key_project.sed.key.evaluation.server.test.testcase.LatexUtilTest;
import org.key_project.sed.key.evaluation.server.test.testcase.PermutationIndexTest;
import org.key_project.sed.key.evaluation.server.test.testcase.ReviewingCodeRandomFormOrderComputerTest;
import org.key_project.sed.key.evaluation.server.test.testcase.SEDServerTest;
import org.key_project.sed.key.evaluation.server.test.testcase.StatisticsUtilTest;
import org.key_project.sed.key.evaluation.server.test.testcase.UnderstandingProofAttemptsRandomFormOrderComputerTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   AbstractRandomCompletionTest.class,
   LatexUtilTest.class,
   PermutationIndexTest.class,
   ReviewingCodeRandomFormOrderComputerTest.class,
   SEDServerTest.class,
   StatisticsUtilTest.class,
   UnderstandingProofAttemptsRandomFormOrderComputerTest.class
})
public class AllEvaluationServerTests {
}