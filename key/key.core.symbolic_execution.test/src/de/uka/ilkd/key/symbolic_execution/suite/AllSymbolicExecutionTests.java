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
package de.uka.ilkd.key.symbolic_execution.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   de.uka.ilkd.key.symbolic_execution.testcase.TestConditionalVariables.class,
   de.uka.ilkd.key.symbolic_execution.testcase.TestExecutionNodePreorderIterator.class,
   de.uka.ilkd.key.symbolic_execution.testcase.TestExecutionNodeWriterAndReader.class,
   de.uka.ilkd.key.symbolic_execution.testcase.TestExecutionVariableExtractor.class,
   de.uka.ilkd.key.symbolic_execution.testcase.TestParallelSiteProofs.class,
   de.uka.ilkd.key.symbolic_execution.testcase.TestTruthValueEvaluationUtil.class,
   de.uka.ilkd.key.symbolic_execution.testcase.TestTruthValueValue.class,
   de.uka.ilkd.key.symbolic_execution.testcase.TestSymbolicLayoutExtractor.class,
   de.uka.ilkd.key.symbolic_execution.testcase.TestSymbolicLayoutWriterAndReader.class,
   de.uka.ilkd.key.symbolic_execution.testcase.TestSymbolicExecutionTreeBuilder.class,
   de.uka.ilkd.key.symbolic_execution.testcase.po.TestFunctionalOperationContractPO.class,
   de.uka.ilkd.key.symbolic_execution.testcase.po.TestProgramMethodPO.class,
   de.uka.ilkd.key.symbolic_execution.testcase.po.TestProgramMethodSubsetPO.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestStepOverSymbolicExecutionTreeNodesStopCondition.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestStepReturnSymbolicExecutionTreeNodesStopCondition.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestSymbolicExecutionStrategy.class,
   de.uka.ilkd.key.symbolic_execution.testcase.util.TestDefaultEntry.class,
   de.uka.ilkd.key.symbolic_execution.testcase.util.TestEqualsHashCodeResetter.class,
   de.uka.ilkd.key.symbolic_execution.testcase.util.TestSideProofStore.class,
   de.uka.ilkd.key.symbolic_execution.testcase.util.TestSymbolicExecutionUtil.class,
   de.uka.ilkd.key.symbolic_execution.testcase.slicing.TestThinBackwardSlicer.class,
   
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestExceptionBreakpointStopConditionCaughtOrUncaught.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestExceptionBreakpointStopConditionWithHitCount.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestExceptionBreakpointStopConditionWithSubclasses.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestJavaWatchpointStopConditionWithHitCount.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestLineBreakpointStopConditionSimpleWithConditions.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestLineBreakpointStopConditionSimpleWithHitCount.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestMethodBreakpointWithConditions.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestKeYWatchpointGlobalVariablesOnSatisfiable.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestKeYWatchpointGlobalVariablesOnTrueWithHitCount.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestKeYWatchpointMethodsOnSatisfiable.class,
   de.uka.ilkd.key.symbolic_execution.testcase.strategy.TestMethodBreakpointWithHitCount.class
})
public class AllSymbolicExecutionTests {
}