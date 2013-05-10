// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * <p>
 * Tests for {@link SymbolicExecutionTreeBuilder},
 * {@link ExecutedSymbolicExecutionTreeNodesStopCondition} and
 * {@link SymbolicExecutionGoalChooser}.
 * </p>
 * <p>
 * This test needs access to the checkout of the KeY repository defined
 * via Java System Property {@code key.home}, e.g. via VM argument:
 * {@code -Dkey.home=D:\Forschung\GIT\KeY}
 * </p>
 * @author Martin Hentschel
 */
public class TestSymbolicExecutionTreeBuilder extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumFor
    */
   public void testUseLoopInvariantArraySumFor() throws Exception {
      // TODO: Activate test if loop invariants are supported (branch condition is implemented)
//      doTest(keyRepDirectory, 
//             "examples/_testcase/set/useLoopInvariantArraySumFor/test/ArraySumFor.java", 
//             "ArraySumFor", 
//             "sum", 
//             "examples/_testcase/set/useLoopInvariantArraySumFor/oracle/ArraySumFor.xml",
//             false,
//             false,
//             DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
//             false,
//             true,
//             true);
   }
   
   /**
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumForEach
    */
   public void testUseLoopInvariantArraySumForEach() throws Exception {
      // TODO: Activate test if loop invariants are supported (branch condition is implemented)
//      doTest(keyRepDirectory, 
//             "examples/_testcase/set/useLoopInvariantArraySumForEach/test/ArraySumForEach.java", 
//             "ArraySumForEach", 
//             "sum", 
//             "examples/_testcase/set/useLoopInvariantArraySumForEach/oracle/ArraySumForEach.xml",
//             false,
//             false,
//             DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
//             false,
//             true,
//             true);
   }
   
   /**
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumWhile
    */
   public void testUseLoopInvariantArraySumWhile() throws Exception {
      // TODO: Activate test if loop invariants are supported (branch condition is implemented)
//      doTest(keyRepDirectory, 
//             "examples/_testcase/set/useLoopInvariantArraySumWhile/test/ArraySumWhile.java", 
//             "ArraySumWhile", 
//             "sum", 
//             "examples/_testcase/set/useLoopInvariantArraySumWhile/oracle/ArraySumWhile.xml",
//             false,
//             false,
//             DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
//             false,
//             true,
//             true);
   }
   
   /**
    * Tests example: examples/_testcase/set/useLoopInvariantArraySumWhileInitiallyInvalid
    */
   public void testUseLoopInvariantArraySumWhileInitiallyInvalid() throws Exception {
      // TODO: Activate test if loop invariants are supported (branch condition is implemented)
//      doTest(keyRepDirectory, 
//             "examples/_testcase/set/useLoopInvariantArraySumWhileInitiallyInvalid/test/ArraySumWhileInitiallyInvalid.java", 
//             "ArraySumWhileInitiallyInvalid", 
//             "sum", 
//             "examples/_testcase/set/useLoopInvariantArraySumWhileInitiallyInvalid/oracle/ArraySumWhileInitiallyInvalid.xml",
//             false,
//             false,
//             DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
//             false,
//             true,
//             true);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractAllBranchesOpenTest
    */
   public void testUseOperationContractAllBranchesOpenTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractAllBranchesOpenTest/test/UseOperationContractAllBranchesOpenTest.java", 
                "UseOperationContractAllBranchesOpenTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractAllBranchesOpenTest/oracle/UseOperationContractAllBranchesOpenTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/identicalTermsDuringProof
    */
   public void testIdenticalTermsDuringProof() throws Exception {
      // Make sure that correct symbolic execution tree is created.
      SymbolicExecutionEnvironment<CustomConsoleUserInterface> env = doSETTest(keyRepDirectory, 
                                                                               "examples/_testcase/set/identicalTermsDuringProof/test/IdenticalTermsDuringProof.java", 
                                                                               "IdenticalTermsDuringProof", 
                                                                               "mid", 
                                                                               null,
                                                                               "examples/_testcase/set/identicalTermsDuringProof/oracle/IdenticalTermsDuringProof.xml",
                                                                               false,
                                                                               false,
                                                                               ALL_IN_ONE_RUN,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false);
      try {
         // Find both statements "mid = y;".
         IExecutionStartNode startNode = env.getBuilder().getStartNode();
         IExecutionMethodCall methodCall = (IExecutionMethodCall)startNode.getChildren()[0];
         IExecutionStatement intMidZ = (IExecutionStatement)methodCall.getChildren()[0];
         IExecutionBranchNode ifYZ = (IExecutionBranchNode)intMidZ.getChildren()[0];
         IExecutionBranchCondition notXY = (IExecutionBranchCondition)ifYZ.getChildren()[0];
         IExecutionBranchNode ifXZ = (IExecutionBranchNode)notXY.getChildren()[0];
         IExecutionBranchCondition not1X = (IExecutionBranchCondition)ifXZ.getChildren()[0];
         IExecutionStatement midThenBranch = (IExecutionStatement)not1X.getChildren()[0];
         IExecutionBranchCondition not1Y = (IExecutionBranchCondition)ifYZ.getChildren()[1];
         IExecutionStatement midElseBranch = (IExecutionStatement)not1Y.getChildren()[0];
         // Make sure that both statements "mid = y;" have the correct position info.
         assertNotSame(midThenBranch, midElseBranch);
         assertNotSame(midThenBranch.getActiveStatement(), midElseBranch.getActiveStatement());
         PositionInfo thenPosition = midThenBranch.getActivePositionInfo();
         PositionInfo elsePosition = midElseBranch.getActivePositionInfo();
         assertNotSame(thenPosition, elsePosition);
         assertNotSame(PositionInfo.UNDEFINED, thenPosition);
         assertNotSame(PositionInfo.UNDEFINED, elsePosition);
         assertEquals(6, thenPosition.getStartPosition().getLine());
         assertEquals(21, thenPosition.getStartPosition().getColumn());
         assertEquals(6, thenPosition.getEndPosition().getLine());
         assertEquals(24, thenPosition.getEndPosition().getColumn());
         assertEquals(9, elsePosition.getStartPosition().getLine());
         assertEquals(17, elsePosition.getStartPosition().getColumn());
         assertEquals(9, elsePosition.getEndPosition().getLine());
         assertEquals(20, elsePosition.getEndPosition().getColumn());
      }
      finally {
         env.dispose();
      }
   }
   
   /**
    * Tests example: examples/_testcase/set/labelTest
    */
   public void testLabelTest_doubled() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/labelTest/test/LabelTest.java", 
                "LabelTest", 
                "doubled", 
                null,
                "examples/_testcase/set/labelTest/oracle/LabelTest_doubled.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/labelTest
    */
   public void testLabelTest_lost() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/labelTest/test/LabelTest.java", 
                "LabelTest", 
                "lost", 
                null,
                "examples/_testcase/set/labelTest/oracle/LabelTest_lost.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/emptyBlockTest
    */
   public void testEmptyBlockTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/emptyBlockTest/test/EmptyBlockTest.java", 
                "EmptyBlockTest", 
                "emptyBlocks", 
                null,
                "examples/_testcase/set/emptyBlockTest/oracle/EmptyBlockTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractExceptionalNoPreconditionWithNullCheckTest
    */
   public void testUseOperationContractExceptionalNoPreconditionWithNullCheckTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractExceptionalNoPreconditionWithNullCheckTest/test/UseOperationContractExceptionalNoPreconditionWithNullCheckTest.java", 
                "UseOperationContractExceptionalNoPreconditionWithNullCheckTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractExceptionalNoPreconditionWithNullCheckTest/oracle/UseOperationContractExceptionalNoPreconditionWithNullCheckTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractFalsePreconditionTest
    */
   public void testUseOperationContractFalsePreconditionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractFalsePreconditionTest/test/UseOperationContractFalsePreconditionTest.java", 
                "UseOperationContractFalsePreconditionTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractFalsePreconditionTest/oracle/UseOperationContractFalsePreconditionTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractFixedNormalPostTest
    */
   public void testUseOperationContractFixedNormalPostTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractFixedNormalPostTest/test/UseOperationContractFixedNormalPostTest.java", 
                "UseOperationContractFixedNormalPostTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractFixedNormalPostTest/oracle/UseOperationContractFixedNormalPostTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractInvalidPreconditionOnObjectTest
    */
   public void testUseOperationContractInvalidPreconditionOnObjectTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractInvalidPreconditionOnObjectTest/test/UseOperationContractInvalidPreconditionOnObjectTest.java", 
                "UseOperationContractInvalidPreconditionOnObjectTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractInvalidPreconditionOnObjectTest/oracle/UseOperationContractInvalidPreconditionOnObjectTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractInvalidPreconditionTest
    */
   public void testUseOperationContractInvalidPreconditionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractInvalidPreconditionTest/test/UseOperationContractInvalidPreconditionTest.java", 
                "UseOperationContractInvalidPreconditionTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractInvalidPreconditionTest/oracle/UseOperationContractInvalidPreconditionTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNoExceptionTest
    */
   public void testUseOperationContractNoExceptionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNoExceptionTest/test/UseOperationContractNoExceptionTest.java", 
                "UseOperationContractNoExceptionTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNoExceptionTest/oracle/UseOperationContractNoExceptionTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNoPreconditionTest
    */
   public void testUseOperationContractNoPreconditionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNoPreconditionTest/test/UseOperationContractNoPreconditionTest.java", 
                "UseOperationContractNoPreconditionTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNoPreconditionTest/oracle/UseOperationContractNoPreconditionTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNoPreconditionWithNullCheckTest
    */
   public void testUseOperationContractNoPreconditionWithNullCheckTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNoPreconditionWithNullCheckTest/test/UseOperationContractNoPreconditionWithNullCheckTest.java", 
                "UseOperationContractNoPreconditionWithNullCheckTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNoPreconditionWithNullCheckTest/oracle/UseOperationContractNoPreconditionWithNullCheckTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNormalAndExceptionalBranchTest
    */
   public void testUseOperationContractNormalAndExceptionalBranchTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNormalAndExceptionalBranchTest/test/UseOperationContractNormalAndExceptionalBranchTest.java", 
                "UseOperationContractNormalAndExceptionalBranchTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNormalAndExceptionalBranchTest/oracle/UseOperationContractNormalAndExceptionalBranchTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/useOperationContractNormalAndExceptionalTogetherTest
    */
   public void testUseOperationContractNormalAndExceptionalTogetherTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/useOperationContractNormalAndExceptionalTogetherTest/test/UseOperationContractNormalAndExceptionalTogetherTest.java", 
                "UseOperationContractNormalAndExceptionalTogetherTest", 
                "main", 
                null,
                "examples/_testcase/set/useOperationContractNormalAndExceptionalTogetherTest/oracle/UseOperationContractNormalAndExceptionalTogetherTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexConstructorTest
    */
   public void testComplexConstructorTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/complexConstructorTest/test/ComplexConstructorTest.java", 
                "ComplexConstructorTest", 
                "main", 
                null,
                "examples/_testcase/set/complexConstructorTest/oracle/ComplexConstructorTest.xml",
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleConstructorTest
    */
   public void testSimpleConstructorTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/simpleConstructorTest/test/SimpleConstructorTest.java", 
                "SimpleConstructorTest", 
                "main", 
                null,
                "examples/_testcase/set/simpleConstructorTest/oracle/SimpleConstructorTest.xml",
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesUnknownTest
    */
   public void testVariablesUnknownTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesUnknownTest/test/UnknownTest.java", 
                          "UnknownTest", 
                          "main", 
                          null,
                          "examples/_testcase/set/variablesUnknownTest/oracle/UnknownTest.xml",
                          true,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesParameterAttributesChange
    */
   public void testElseIfTest_variablesParameterAttributesChange() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/variablesParameterAttributesChange/test/VariablesParameterAttributesChange.java", 
                "VariablesParameterAttributesChange", 
                "main", 
                null,
                "examples/_testcase/set/variablesParameterAttributesChange/oracle/VariablesParameterAttributesChange.xml",
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfTest
    */
   public void testElseIfTest_mergedBranchConditions() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/elseIfTest/test/ElseIfTest.java", 
                "ElseIfTest", 
                "elseIf", 
                null,
                "examples/_testcase/set/elseIfTest/oracle/ElseIfTestMergedBranchConditions.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                true,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/switchCaseTest
    */
   public void testSwitchCaseTest_mergedBranchConditions() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/switchCaseTest/test/SwitchCaseTest.java", 
                "SwitchCaseTest", 
                "switchCase", 
                null,
                "examples/_testcase/set/switchCaseTest/oracle/SwitchCaseTestMergedBranchConditions.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                true,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/loopIterationTest
    */
   public void testLoopIteration_LoopWithMethod() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/loopIterationTest/test/LoopIterationTest.java", 
                "LoopIterationTest", 
                "loopMultipleTimes", 
                null,
                "examples/_testcase/set/loopIterationTest/oracle/LoopIterationTest_loopMultipleTimes.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/loopIterationTest
    */
   public void testLoopIteration_LoopStatementCopied() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/loopIterationTest/test/LoopIterationTest.java", 
                "LoopIterationTest", 
                "mainWorks", 
                null,
                "examples/_testcase/set/loopIterationTest/oracle/LoopIterationTest_mainWorks.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/loopIterationTest
    */
   public void testLoopIteration_LoopStatementReused() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/loopIterationTest/test/LoopIterationTest.java", 
                "LoopIterationTest", 
                "main", 
                null,
                "examples/_testcase/set/loopIterationTest/oracle/LoopIterationTest_main.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesArrayTest
    */
   public void testVariablesArrayTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesArrayTest/test/VariablesArrayTest.java", 
                          "VariablesArrayTest", 
                          "main", 
                          null,
                          "examples/_testcase/set/variablesArrayTest/oracle/VariablesArrayTest.xml",
                          true,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesInstanceVariableTest
    */
   public void testVariablesInstanceVariableTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesInstanceVariableTest/test/VariablesInstanceVariableTest.java", 
                          "VariablesInstanceVariableTest", 
                          "main", 
                          null,
                          "examples/_testcase/set/variablesInstanceVariableTest/oracle/VariablesInstanceVariableTest.xml",
                          true,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesLocalTest
    */
   public void testVariablesLocalTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesLocalTest/test/VariablesLocalTest.java", 
                          "VariablesLocalTest", 
                          "main", 
                          null,
                          "examples/_testcase/set/variablesLocalTest/oracle/VariablesLocalTest.xml",
                          true,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesStaticTest
    */
   public void testVariablesStaticTest() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/variablesStaticTest/test/VariablesStaticTest.java", 
                          "VariablesStaticTest", 
                          "main", 
                          null,
                          "examples/_testcase/set/variablesStaticTest/oracle/VariablesStaticTest.xml",
                          true,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexFlatSteps
    */
   public void testComplexFlatSteps() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/complexFlatSteps/test/ComplexFlatSteps.java", 
                "ComplexFlatSteps", 
                "doSomething", 
                null,
                "examples/_testcase/set/complexFlatSteps/oracle/ComplexFlatSteps.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexIf
    */
   public void testComplexIf() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/complexIf/test/ComplexIf.java", 
                "ComplexIf", 
                "min", 
                null,
                "examples/_testcase/set/complexIf/oracle/ComplexIf.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/doWhileFalseTest
    */
   public void testDoWhileFlaseTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/doWhileFalseTest/test/DoWhileFalseTest.java", 
                "DoWhileFalseTest", 
                "main", 
                null,
                "examples/_testcase/set/doWhileFalseTest/oracle/DoWhileFalseTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/doWhileTest
    */
   public void testDoWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/doWhileTest/test/DoWhileTest.java", 
                "DoWhileTest", 
                "main", 
                null,
                "examples/_testcase/set/doWhileTest/oracle/DoWhileTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfDifferentVariables
    */
   public void testElseIfDifferentVariables() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/elseIfDifferentVariables/test/ElseIfDifferentVariables.java", 
                "ElseIfDifferentVariables", 
                "main", 
                null,
                "examples/_testcase/set/elseIfDifferentVariables/oracle/ElseIfDifferentVariables.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfTest
    */
   public void testElseIfTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/elseIfTest/test/ElseIfTest.java", 
                "ElseIfTest", 
                "elseIf", 
                null,
                "examples/_testcase/set/elseIfTest/oracle/ElseIfTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/fixedRecursiveMethodCallTest
    */
   public void testFixedRecursiveMethodCallTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/fixedRecursiveMethodCallTest/test/FixedRecursiveMethodCallTest.java", 
                "FixedRecursiveMethodCallTest", 
                "decreaseValue", 
                null,
                "examples/_testcase/set/fixedRecursiveMethodCallTest/oracle/FixedRecursiveMethodCallTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/forEachTest
    */
   public void testForEachTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/forEachTest/test/ForEachTest.java", 
                "ForEachTest", 
                "main", 
                null,
                "examples/_testcase/set/forEachTest/oracle/ForEachTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/forFalseTest
    */
   public void testForFalseTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/forFalseTest/test/ForFalseTest.java", 
                "ForFalseTest", 
                "main", 
                null,
                "examples/_testcase/set/forFalseTest/oracle/ForFalseTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/forTest
    */
   public void testForTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/forTest/test/ForTest.java", 
                "ForTest", 
                "main", 
                null,
                "examples/_testcase/set/forTest/oracle/ForTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalDoWhileTest
    */
   public void testFunctionalDoWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/functionalDoWhileTest/test/FunctionalDoWhileTest.java", 
                "FunctionalDoWhileTest", 
                "main", 
                null,
                "examples/_testcase/set/functionalDoWhileTest/oracle/FunctionalDoWhileTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalForTest
    */
   public void testFunctionalForTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/functionalForTest/test/FunctionalForTest.java", 
                "FunctionalForTest", 
                "main", 
                null,
                "examples/_testcase/set/functionalForTest/oracle/FunctionalForTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalIf
    */
   public void testFunctionalIf() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/functionalIf/test/FunctionalIf.java", 
                "FunctionalIf", 
                "min", 
                null,
                "examples/_testcase/set/functionalIf/oracle/FunctionalIf.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalWhileTest
    */
   public void testFunctionalWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/functionalWhileTest/test/FunctionalWhileTest.java", 
                "FunctionalWhileTest", 
                "main", 
                null,
                "examples/_testcase/set/functionalWhileTest/oracle/FunctionalWhileTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallOnObject
    */
   public void testMethodCallOnObject() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodCallOnObject/test/MethodCallOnObject.java", 
                "MethodCallOnObject", 
                "main", 
                null,
                "examples/_testcase/set/methodCallOnObject/oracle/MethodCallOnObject.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallOnObjectWithException
    */
   public void testMethodCallOnObjectWithException() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodCallOnObjectWithException/test/MethodCallOnObjectWithException.java", 
                "MethodCallOnObjectWithException", 
                "main", 
                null,
                "examples/_testcase/set/methodCallOnObjectWithException/oracle/MethodCallOnObjectWithException.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallParallelTest
    */
   public void testMethodCallParallelTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodCallParallelTest/test/MethodCallParallelTest.java", 
                "MethodCallParallelTest", 
                "main", 
                null,
                "examples/_testcase/set/methodCallParallelTest/oracle/MethodCallParallelTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodFormatTest
    */
   public void testMethodFormatTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodFormatTest/test/MethodFormatTest.java", 
                "MethodFormatTest", 
                "main", 
                null,
                "examples/_testcase/set/methodFormatTest/oracle/MethodFormatTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodHierarchyCallTest
    */
   public void testMethodHierarchyCallTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodHierarchyCallTest/test/MethodHierarchyCallTest.java", 
                "MethodHierarchyCallTest", 
                "main", 
                null,
                "examples/_testcase/set/methodHierarchyCallTest/oracle/MethodHierarchyCallTest.xml",
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodHierarchyCallWithExceptionTest
    */
   public void testMethodHierarchyCallWithExceptionTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/methodHierarchyCallWithExceptionTest/test/MethodHierarchyCallWithExceptionTest.java", 
                "MethodHierarchyCallWithExceptionTest", 
                "main", 
                null,
                "examples/_testcase/set/methodHierarchyCallWithExceptionTest/oracle/MethodHierarchyCallWithExceptionTest.xml",
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedDoWhileTest
    */
   public void testNestedDoWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/nestedDoWhileTest/test/NestedDoWhileTest.java", 
                "NestedDoWhileTest", 
                "main", 
                null,
                "examples/_testcase/set/nestedDoWhileTest/oracle/NestedDoWhileTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedForTest
    */
   public void testNestedForTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/nestedForTest/test/NestedForTest.java", 
                "NestedForTest", 
                "main", 
                null,
                "examples/_testcase/set/nestedForTest/oracle/NestedForTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedWhileTest
    */
   public void testNestedWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/nestedWhileTest/test/NestedWhileTest.java", 
                "NestedWhileTest", 
                "mainNested", 
                 null,
                "examples/_testcase/set/nestedWhileTest/oracle/NestedWhileTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: examples/_testcase/set/recursiveFibonacci
    * </p>
    * <p>
    * This test produces a deep symbolic execution tree to make sure
    * that no {@link StackOverflowError}s are thrown.
    * </p>
    */
   public void testRecursiveFibonacci_LONG_RUNNING_TEST() throws Exception {
      doSETTestAndDispose(keyRepDirectory, 
                          "examples/_testcase/set/recursiveFibonacci/test/RecursiveFibonacci.java", 
                          "RecursiveFibonacci", 
                          "fibonacci10", 
                          null,
                          "examples/_testcase/set/recursiveFibonacci/oracle/RecursiveFibonacci.xml",
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleIf
    */
   public void testSimpleIf() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/simpleIf/test/SimpleIf.java", 
                "SimpleIf", 
                "min", 
                null,
                "examples/_testcase/set/simpleIf/oracle/SimpleIf.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleNullPointerSplitTest
    */
   public void testSimpleNullPointerSplitTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/simpleNullPointerSplitTest/test/SimpleNullPointerSplitTest.java", 
                "SimpleNullPointerSplitTest", 
                "main", 
                null,
                "examples/_testcase/set/simpleNullPointerSplitTest/oracle/SimpleNullPointerSplitTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/statementKindTest
    */
   public void testStatementKindTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/statementKindTest/test/StatementKindTest.java", 
                "StatementKindTest", 
                "main", 
                null,
                "examples/_testcase/set/statementKindTest/oracle/StatementKindTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/statements
    */
   public void testStatements() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/statements/test/FlatSteps.java", 
                "FlatSteps", 
                "doSomething", 
                null,
                "examples/_testcase/set/statements/oracle/FlatSteps.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticMethodCall
    */
   public void testStaticMethodCall() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/staticMethodCall/test/StaticMethodCall.java", 
                "StaticMethodCall", 
                "main", 
                null,
                "examples/_testcase/set/staticMethodCall/oracle/StaticMethodCall.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/switchCaseTest
    */
   public void testSwitchCaseTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/switchCaseTest/test/SwitchCaseTest.java", 
                "SwitchCaseTest", 
                "switchCase", 
                null,
                "examples/_testcase/set/switchCaseTest/oracle/SwitchCaseTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/throwTest
    */
   public void testThrowTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/throwTest/test/ThrowTest.java", 
                "ThrowTest", 
                "main", 
                null,
                "examples/_testcase/set/throwTest/oracle/ThrowTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/throwVariableTest
    */
   public void testThrowVariableTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/throwVariableTest/test/ThrowVariableTest.java", 
                "ThrowVariableTest", 
                "main", 
                null,
                "examples/_testcase/set/throwVariableTest/oracle/ThrowVariableTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/tryCatchFinally
    */
   public void testTryCatchFinally() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/tryCatchFinally/test/TryCatchFinally.java", 
                "TryCatchFinally", 
                "tryCatchFinally", 
                null,
                "examples/_testcase/set/tryCatchFinally/oracle/TryCatchFinally.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/whileFalseTest
    */
   public void testWhileFalseTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/whileFalseTest/test/WhileFalseTest.java", 
                "WhileFalseTest", 
                "main", 
                null,
                "examples/_testcase/set/whileFalseTest/oracle/WhileFalseTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: examples/_testcase/set/whileTest
    */
   public void testWhileTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/whileTest/test/WhileTest.java", 
                "WhileTest", 
                "main", 
                null,
                "examples/_testcase/set/whileTest/oracle/WhileTest.xml",
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false);
   }
}
