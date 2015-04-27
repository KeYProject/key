// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.testcase;

import java.io.File;
import java.util.HashMap;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder.SymbolicExecutionCompletions;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchStatement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStatement;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

/**
 * Tests for {@link SymbolicExecutionTreeBuilder},
 * {@link ExecutedSymbolicExecutionTreeNodesStopCondition} and
 * {@link SymbolicExecutionGoalChooser}.
 * @author Martin Hentschel
 */
public class TestSymbolicExecutionTreeBuilder extends AbstractSymbolicExecutionTestCase {
   
   /**
    * Tests example: /set/instanceOfNotInEndlessLoop in the Symbolic Execution Profile
    * and ensures that no rules are applied forever.
    */
   public void testInstanceOfNotInEndlessLoop() throws Exception {
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = doSETTest(testCaseDirectory, 
                                                                        "/set/instanceOfNotInEndlessLoop/test/Number.java", 
                                                                        "Number", 
                                                                        "equals", 
                                                                        null,
                                                                        "/set/instanceOfNotInEndlessLoop/oracle/Number.xml",
                                                                        false,
                                                                        false,
                                                                        false,
                                                                        false,
                                                                        ALL_IN_ONE_RUN,
                                                                        false,
                                                                        false,
                                                                        false,
                                                                        false,
                                                                        false,
                                                                        false,
                                                                        false,
                                                                        false);
      try {
         int nodesCount = env.getProof().countNodes();
         assertTrue(nodesCount >= 100); // Currently 105 nodes are needed, +-5 are acceptable
         assertTrue(nodesCount < 110); // Currently 105 nodes are needed, +-5 are acceptable
      }
      finally {
         if (env != null) {
            env.dispose();
         }
      }
   }
   
   /**
    * Tests example: /set/assumesUserInputTest in the Symbolic Execution Profile
    */
   public void testAssumesUserInputTest() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                "/set/assumesUserInputTest/test/AssumesUserInputTest.proof", 
                "/set/assumesUserInputTest/oracle/AssumesUserInputTest.xml", 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false);
   }
   
   /**
    * Tests example: /set/symbolicExecutionCompletionsTest
    */
   public void testSymbolicExecutionCompletionsTest() throws Exception {
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = null;
      HashMap<String, String> originalTacletOptions = null;
      boolean originalOneStepSimplification = isOneStepSimplificationEnabled(null);
      try {
         String javaPathInBaseDir = "/set/symbolicExecutionCompletionsTest/test/SymbolicExecutionCompletionsTest.java";
         String containerTypeName = "SymbolicExecutionCompletionsTest";
         String methodFullName = "magic";
         // Make sure that the correct taclet options are defined.
         originalTacletOptions = setDefaultTacletOptions(testCaseDirectory, javaPathInBaseDir, containerTypeName, methodFullName);
         setOneStepSimplificationEnabled(null, true);
         // Create proof environment for symbolic execution
         env = createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInBaseDir, containerTypeName, methodFullName, null, false, false, false, false, false, false, false, false);
         IExecutionStart start = env.getBuilder().getStartNode();
         // Perform step into
         SymbolicExecutionCompletions completions = stepInto(env.getUi(), env.getBuilder(), "/set/symbolicExecutionCompletionsTest/oracle/SymbolicExecutionCompletionsTest", 1, ".xml", testCaseDirectory);
         assertNotNull(completions);
         IExecutionNode<?> call = start.getChildren()[0];
         assertEquals(0, completions.getBlockCompletions().length);
         assertEquals(0, completions.getMethodReturns().length);
         // Perform step into
         completions = stepInto(env.getUi(), env.getBuilder(), "/set/symbolicExecutionCompletionsTest/oracle/SymbolicExecutionCompletionsTest", 2, ".xml", testCaseDirectory);
         assertNotNull(completions);
         IExecutionNode<?> ifStatement = call.getChildren()[0];
         assertEquals(0, completions.getBlockCompletions().length);
         assertEquals(0, completions.getMethodReturns().length);
         // Perform step into
         completions = stepInto(env.getUi(), env.getBuilder(), "/set/symbolicExecutionCompletionsTest/oracle/SymbolicExecutionCompletionsTest", 3, ".xml", testCaseDirectory);
         assertNotNull(completions);
         IExecutionNode<?> leftBC = ifStatement.getChildren()[0];
         IExecutionNode<?> rightBC = ifStatement.getChildren()[1];
         IExecutionNode<?> leftReturnStatement = leftBC.getChildren()[0];
         IExecutionNode<?> rightIncrement = rightBC.getChildren()[0];
         assertEquals(1, completions.getBlockCompletions().length);
         assertSame(leftReturnStatement, completions.getBlockCompletions()[0]);
         assertEquals(0, completions.getMethodReturns().length);
         // Perform step into
         completions = stepInto(env.getUi(), env.getBuilder(), "/set/symbolicExecutionCompletionsTest/oracle/SymbolicExecutionCompletionsTest", 4, ".xml", testCaseDirectory);
         assertNotNull(completions);
         IExecutionNode<?> leftReturn = leftReturnStatement.getChildren()[0];
         IExecutionNode<?> rightReturnStatement = rightIncrement.getChildren()[0];
         assertEquals(1, completions.getBlockCompletions().length);
         assertSame(rightReturnStatement, completions.getBlockCompletions()[0]);
         assertEquals(1, completions.getMethodReturns().length);
         assertSame(leftReturn, completions.getMethodReturns()[0]);
         // Perform step into
         completions = stepInto(env.getUi(), env.getBuilder(), "/set/symbolicExecutionCompletionsTest/oracle/SymbolicExecutionCompletionsTest", 5, ".xml", testCaseDirectory);
         assertNotNull(completions);
         IExecutionNode<?> rightReturn = rightReturnStatement.getChildren()[0];
         assertEquals(0, completions.getBlockCompletions().length);
         assertEquals(1, completions.getMethodReturns().length);
         assertSame(rightReturn, completions.getMethodReturns()[0]);
         // Perform step into
         completions = stepInto(env.getUi(), env.getBuilder(), "/set/symbolicExecutionCompletionsTest/oracle/SymbolicExecutionCompletionsTest", 6, ".xml", testCaseDirectory);
         assertNotNull(completions);
         assertEquals(0, completions.getBlockCompletions().length);
         assertEquals(0, completions.getMethodReturns().length);
      }
      finally {
         // Restore original options
         setOneStepSimplificationEnabled(null, originalOneStepSimplification);
         restoreTacletOptions(originalTacletOptions);
         if (env != null) {
            env.dispose();
         }
      }
   }
   
   /**
    * Tests example: /set/allNodeTypesTest in the Java Profile
    */
   public void testAllNodeTypesTest_JavaProfile_NoOneStepSimplification() throws Exception {
      doJavaProfileTest("/set/allNodeTypesTest/test/AllNodeTypesTest_VerificationProfile_NoOneStepSimplification.proof", 
                        "/set/allNodeTypesTest/oracle/AllNodeTypesTest_VerificationProfile_NoOneStepSimplification.xml");
   }
   
   /**
    * Tests example: /set/allNodeTypesTest in the Java Profile
    */
   public void testAllNodeTypesTest_JavaProfile() throws Exception {
      doJavaProfileTest("/set/allNodeTypesTest/test/AllNodeTypesTest_VerificationProfile.proof", 
                        "/set/allNodeTypesTest/oracle/AllNodeTypesTest_VerificationProfile.xml");
   }
   
   /**
    * Loads an existing proof file performed in the {@link JavaProfile}.
    * @param proofFilePathInBaseDir The path to the proof file inside the base directory.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @throws Exception Occurred Exception.
    */
   protected void doJavaProfileTest(String proofFilePathInBaseDir,
                                    String oraclePathInBaseDirFile) throws Exception {
      // Ensure that JavaProfile was used before
      KeYEnvironment<?> env = KeYEnvironment.load(JavaProfile.getDefaultInstance(), new File(testCaseDirectory, proofFilePathInBaseDir), null, null, true);
      env.dispose();
      // Test symbolic execution
      doSETTestAndDispose(testCaseDirectory, 
                proofFilePathInBaseDir, 
                oraclePathInBaseDirFile, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false);
      // Test symbolic execution again when symbolic execution profile was used before.
      doSETTestAndDispose(testCaseDirectory, 
                proofFilePathInBaseDir, 
                oraclePathInBaseDirFile, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false);
   }
   
   /**
    * Tests example: /set/allNodeTypesTest in the Symbolic Execution Profile
    */
   public void testAllNodeTypesTest_SymbolicExecutionProfile() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                "/set/allNodeTypesTest/test/AllNodeTypesTest.proof", 
                "/set/allNodeTypesTest/oracle/AllNodeTypesTest.xml", 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false, 
                false);
   }
   
   /**
    * Tests example: /set/loopStatementBlockTest
    */
   public void testLoopStatementBlockTest_nestedLoop() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/loopStatementBlockTest/test/LoopStatementBlockTest.java", 
                "LoopStatementBlockTest", 
                "nestedLoop", 
                null,
                "/set/loopStatementBlockTest/oracle/LoopStatementBlockTest_nestedLoop.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/loopStatementBlockTest
    */
   public void testLoopStatementBlockTest_simpleLoop() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/loopStatementBlockTest/test/LoopStatementBlockTest.java", 
                "LoopStatementBlockTest", 
                "simpleLoop", 
                null,
                "/set/loopStatementBlockTest/oracle/LoopStatementBlockTest_simpleLoop.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/branchStatementBlockTest
    */
   public void testBranchStatementBlockTest_min() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/branchStatementBlockTest/test/BranchStatementBlockTest.java", 
                "BranchStatementBlockTest", 
                "min", 
                null,
                "/set/branchStatementBlockTest/oracle/BranchStatementBlockTest_min.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/branchStatementBlockTest
    */
   public void testBranchStatementBlockTest_nestedIf() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/branchStatementBlockTest/test/BranchStatementBlockTest.java", 
                "BranchStatementBlockTest", 
                "nestedIf", 
                null,
                "/set/branchStatementBlockTest/oracle/BranchStatementBlockTest_nestedIf.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/branchStatementBlockTest
    */
   public void testBranchStatementBlockTest_simpleBlock() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/branchStatementBlockTest/test/BranchStatementBlockTest.java", 
                "BranchStatementBlockTest", 
                "simpleBlock", 
                null,
                "/set/branchStatementBlockTest/oracle/BranchStatementBlockTest_simpleBlock.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/branchStatementBlockTest
    */
   public void testBranchStatementBlockTest_ifNoBlock() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/branchStatementBlockTest/test/BranchStatementBlockTest.java", 
                "BranchStatementBlockTest", 
                "ifNoBlock", 
                null,
                "/set/branchStatementBlockTest/oracle/BranchStatementBlockTest_ifNoBlock.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/branchStatementBlockTest
    */
   public void testBranchStatementBlockTest_onlyThen() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/branchStatementBlockTest/test/BranchStatementBlockTest.java", 
                "BranchStatementBlockTest", 
                "onlyThen", 
                null,
                "/set/branchStatementBlockTest/oracle/BranchStatementBlockTest_onlyThen.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/branchStatementBlockTest
    */
   public void testBranchStatementBlockTest_onlyElse() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/branchStatementBlockTest/test/BranchStatementBlockTest.java", 
                "BranchStatementBlockTest", 
                "onlyElse", 
                null,
                "/set/branchStatementBlockTest/oracle/BranchStatementBlockTest_onlyElse.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/branchStatementBlockTest
    */
   public void testBranchStatementBlockTest_switchTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/branchStatementBlockTest/test/BranchStatementBlockTest.java", 
                "BranchStatementBlockTest", 
                "switchTest", 
                null,
                "/set/branchStatementBlockTest/oracle/BranchStatementBlockTest_switchTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/branchStatementBlockTest
    */
   public void testBranchStatementBlockTest_onlyEmptyThen() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/branchStatementBlockTest/test/BranchStatementBlockTest.java", 
                "BranchStatementBlockTest", 
                "onlyEmptyThen", 
                null,
                "/set/branchStatementBlockTest/oracle/BranchStatementBlockTest_onlyEmptyThen.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/branchStatementBlockTest
    */
   public void testBranchStatementBlockTest_recursive() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/branchStatementBlockTest/test/BranchStatementBlockTest.java", 
                "BranchStatementBlockTest", 
                "recursiveMain", 
                null,
                "/set/branchStatementBlockTest/oracle/BranchStatementBlockTest_recursive.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/constraintsAfterUsedLoopInvariant
    */
   public void testConstraintsAfterUsedLoopInvariant() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/constraintsAfterUsedLoopInvariant/test/E_Loop.java", 
                "E_Loop", 
                "calculate", 
                null,
                "/set/constraintsAfterUsedLoopInvariant/oracle/E_Loop.xml",
                true,
                true,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/constraintsOfAppliedMethodContract
    */
   public void testConstraintsOfAppliedMethodContract() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/constraintsOfAppliedMethodContract/test/MethodContract.java", 
                "MethodContract", 
                "magic", 
                null,
                "/set/constraintsOfAppliedMethodContract/oracle/MethodContract.xml",
                true,
                true,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/exceptionalMethodReturnTest
    */
   public void testExceptionalMethodReturnTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/exceptionalMethodReturnTest/test/ExceptionalMethodReturnTest.java", 
                "ExceptionalMethodReturnTest", 
                "main", 
                null,
                "/set/exceptionalMethodReturnTest/oracle/ExceptionalMethodReturnTest.xml",
                false,
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/exceptionalMethodReturnTestWithLoop
    */
   public void testExceptionalMethodReturnTestWithLoop() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/exceptionalMethodReturnTestWithLoop/test/Loop.java", 
                "Loop", 
                "magic", 
                null,
                "/set/exceptionalMethodReturnTestWithLoop/oracle/Loop.xml",
                false,
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticInstanceFieldChanged
    */
   public void testStaticInstanceFieldChanged() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticInstanceFieldChanged/test/StaticInstanceFieldChanged.java", 
                "StaticInstanceFieldChanged", 
                "magic", 
                null,
                "/set/staticInstanceFieldChanged/oracle/StaticInstanceFieldChanged.xml",
                false,
                true,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractVariableNestedOperationContractUse
    */
   public void testUseOperationContractVariableNestedOperationContractUse() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractVariableNestedOperationContractUse/test/VariableNestedOperationContractUse.java", 
                "VariableNestedOperationContractUse", 
                "main", 
                null,
                "/set/useOperationContractVariableNestedOperationContractUse/oracle/VariableNestedOperationContractUse.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractApplyContractTwice
    */
   public void testUseOperationContractApplyContractTwice() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractApplyContractTwice/test/OperationContractAppliedTwiceTest.java", 
                "OperationContractAppliedTwiceTest", 
                "doubleMagic", 
                null,
                "/set/useOperationContractApplyContractTwice/oracle/OperationContractAppliedTwiceTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/verificationProofFile_VerifyNumber
    */
   public void testVerifyNumberNormal() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                "/set/verificationProofFile_VerifyNumber/test/VerifyNumberNormal.proof",
                "/set/verificationProofFile_VerifyNumber/oracle/VerifyNumberNormal.xml",
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/verificationProofFile_VerifyMin
    */
   public void testVerifyMinTrueBranch() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                "/set/verificationProofFile_VerifyMin/test/VerifyMinTrueBranch.proof",
                "/set/verificationProofFile_VerifyMin/oracle/VerifyMinTrueBranch.xml",
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/verificationProofFile_VerifyMin
    */
   public void testVerifyMin() throws Exception {
      doSETTestAndDispose(testCaseDirectory,
                "/set/verificationProofFile_VerifyMin/test/VerifyMin.proof",
                "/set/verificationProofFile_VerifyMin/oracle/VerifyMin.xml",
                false,
                true,
                true,
                true,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/simpleMethodCallStackTest
    */
   public void testSimpleMethodCallStack() throws Exception {
      doSETTest(testCaseDirectory,
                "/set/simpleMethodCallStackTest/test/SimpleMethodCallStackTest.java",
                "SimpleMethodCallStackTest",
                "magic",
                null,
                "/set/simpleMethodCallStackTest/oracle/SimpleMethodCallStackTest.xml",
                false,
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/methodCallStackTest
    */
   public void testMethodCallStack() throws Exception {
      doSETTest(testCaseDirectory,
                "/set/methodCallStackTest/test/MethodCallStackTest.java",
                "MethodCallStackTest",
                "magic",
                null,
                "/set/methodCallStackTest/oracle/MethodCallStackTest.xml",
                false,
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/unicodeTest
    */
   public void testUnicode_Disabled() throws Exception {
      doSETTest(testCaseDirectory,
                "/set/unicodeTest/test/UnicodeTest.java",
                "UnicodeTest",
                "magic",
                null,
                "/set/unicodeTest/oracle/UnicodeTest_Disabled.xml",
                false,
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                true,
                false);
   }
   
   /**
    * Tests example: /set/unicodeTest
    */
   public void testUnicode_Enabled() throws Exception {
      doSETTest(testCaseDirectory,
                "/set/unicodeTest/test/UnicodeTest.java",
                "UnicodeTest",
                "magic",
                null,
                "/set/unicodeTest/oracle/UnicodeTest_Enabled.xml",
                false,
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                true,
                true,
                false);
   }
   
   /**
    * Tests example: /set/prettyPrint
    */
   public void testPrettyPrinting_Disabled() throws Exception {
      doSETTest(testCaseDirectory,
                "/set/prettyPrint/test/PrettyPrintTest.java",
                "PrettyPrintTest",
                "main",
                null,
                "/set/prettyPrint/oracle/PrettyPrintTest_Disabled.xml",
                false,
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/prettyPrint
    */
   public void testPrettyPrinting_Enabled() throws Exception {
      doSETTest(testCaseDirectory,
                "/set/prettyPrint/test/PrettyPrintTest.java",
                "PrettyPrintTest",
                "main",
                null,
                "/set/prettyPrint/oracle/PrettyPrintTest_Enabled.xml",
                false,
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                true,
                false);
   }
   
   /**
    * Tests example: /set/useLoopInvariantAndOperationContractStrictlyPure
    */
   public void testLoopInvariantAndOperationContractStrictlyPure() throws Exception {
      doSETTest(testCaseDirectory,
                "/set/useLoopInvariantAndOperationContractStrictlyPure/test/IndexOf.java",
                "IndexOf",
                "indexOf",
                null,
                "/set/useLoopInvariantAndOperationContractStrictlyPure/oracle/IndexOf.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false,
                false);
   }

   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainVoidMethod() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainVoidMethod", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainVoidMethod.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainNoArgs() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainNoArgs", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainNoArgs.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainResult() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainResult", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainResult.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainResultNotSpecified() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainResultNotSpecified", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainResultNotSpecified.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainExceptinalVoid() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainExceptinalVoid", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainExceptinalVoid.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainExceptinalUnused() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainExceptinalUnused", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainExceptinalUnused.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainExceptinal() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainExceptinal", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainExceptinal.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainBooleanResultUnused() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainBooleanResultUnused", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainBooleanResultUnused.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainBooleanResultUnspecifiedUnused() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainBooleanResultUnspecifiedUnused", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainBooleanResultUnspecifiedUnused.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainExceptionalConstructor() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainExceptionalConstructor", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainExceptionalConstructor.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainConstructor() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainConstructor", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainConstructor.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/instanceContractTest
    */
   public void testInstanceContractTest_mainOnObject() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/instanceContractTest/test/InstanceContractTest.java", 
                "InstanceContractTest", 
                "mainOnObject", 
                null,
                "/set/instanceContractTest/oracle/InstanceContractTest_mainOnObject.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainVoidMethod() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainVoidMethod", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainVoidMethod.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainNoArgs() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainNoArgs", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainNoArgs.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainResult() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainResult", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainResult.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainResultNotSpecified() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainResultNotSpecified", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainResultNotSpecified.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainExceptinalVoid() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainExceptinalVoid", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainExceptinalVoid.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainExceptinalUnused() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainExceptinalUnused", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainExceptinalUnused.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainExceptinal() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainExceptinal", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainExceptinal.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainBooleanResultUnused() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainBooleanResultUnused", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainBooleanResultUnused.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainBooleanResultUnspecifiedUnused() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainBooleanResultUnspecifiedUnused", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainBooleanResultUnspecifiedUnused.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainExceptionalConstructor() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainExceptionalConstructor", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainExceptionalConstructor.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainConstructor() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainConstructor", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainConstructor.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticContractTest
    */
   public void testStaticContractTest_mainOnObject() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticContractTest/test/StaticContractTest.java", 
                "StaticContractTest", 
                "mainOnObject", 
                null,
                "/set/staticContractTest/oracle/StaticContractTest_mainOnObject.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/verifiedTest
    */
   public void testVerifiedTest_notLoop() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::notLoop(int)].JML operation contract.0", 
                "/set/verifiedTest/oracle/VerifiedTest_notLoop.xml",
                false,
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }

   /**
    * Tests example: /set/verifiedTest
    */
   public void testVerifiedTest_loop() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::loop(int)].JML operation contract.0", 
                "/set/verifiedTest/oracle/VerifiedTest_loop.xml",
                false,
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }

   /**
    * Tests example: /set/verifiedTest
    */
   public void testVerifiedTest_notMagic() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::notMagic()].JML operation contract.0", 
                "/set/verifiedTest/oracle/VerifiedTest_notMagic.xml",
                false,
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }

   /**
    * Tests example: /set/verifiedTest
    */
   public void testVerifiedTest_magic() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::magic()].JML operation contract.0", 
                "/set/verifiedTest/oracle/VerifiedTest_magic.xml",
                false,
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/verifiedTest
    */
   public void testVerifiedTest_notMagicException() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::notMagicException()].JML exceptional_behavior operation contract.0", 
                "/set/verifiedTest/oracle/VerifiedTest_notMagicException.xml",
                false,
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/verifiedTest
    */
   public void testVerifiedTest_magicException() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/verifiedTest/test/VerifiedTest.java", 
                "VerifiedTest[VerifiedTest::magicException()].JML exceptional_behavior operation contract.0", 
                "/set/verifiedTest/oracle/VerifiedTest_magicException.xml",
                false,
                false,
                false,
                false,
                ALL_IN_ONE_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/methodCallReturnTests
    */
   public void testMethodCallReturnTests() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/methodCallReturnTests/test/MethodCallReturnTests.java", 
                "MethodCallReturnTests", 
                "main", 
                null,
                "/set/methodCallReturnTests/oracle/MethodCallReturnTests.xml",
                false,
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useLoopInvariantArrayAverage
    */
   public void testUseLoopInvariantArrayAverage() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArrayAverage/test/ArrayAverage.java", 
                "ArrayAverage", 
                "average", 
                null,
                "/set/useLoopInvariantArrayAverage/oracle/ArrayAverage.xml",
                false,
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractStatementsInImpliciteConstructor
    */
   public void testUseOperationContractStatementsInImpliciteConstructor() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractStatementsInImpliciteConstructor/test/UseOperationContractStatementsInImpliciteConstructor.java", 
                "UseOperationContractStatementsInImpliciteConstructor", 
                "average", 
                null,
                "/set/useOperationContractStatementsInImpliciteConstructor/oracle/UseOperationContractStatementsInImpliciteConstructor.xml",
                false,
                true,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantLoopSplittingCondition
    * </p>
    * <p>
    * Tests the handling of method returns in different modalities.
    * </p>
    */
   public void testUseLoopInvariantLoopSplittingCondition() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantLoopSplittingCondition/test/LoopSplittingCondition.java", 
                "LoopSplittingCondition", 
                "main", 
                null,
                "/set/useLoopInvariantLoopSplittingCondition/oracle/LoopSplittingCondition.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantTwoLoops
    * </p>
    * <p>
    * Tests the handling of method returns in different modalities.
    * </p>
    */
   public void testUseLoopInvariantTwoLoops() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantTwoLoops/test/TwoLoops.java", 
                "TwoLoops", 
                "main", 
                null,
                "/set/useLoopInvariantTwoLoops/oracle/TwoLoops.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantWhileWithMethodCallAsConditionFullImplemented
    * </p>
    * <p>
    * Tests the handling of method returns in different modalities.
    * </p>
    */
   public void testLoopInvariantMethodReturnInDifferentModalities() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantWhileWithMethodCallAsConditionFullImplemented/test/WhileWithMethodCallAsConditionFullImplemented.java", 
                "WhileWithMethodCallAsConditionFullImplemented", 
                "size", 
                null,
                "/set/useLoopInvariantWhileWithMethodCallAsConditionFullImplemented/oracle/WhileWithMethodCallAsConditionFullImplemented.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantLoopBodyBranchClosed
    * </p>
    * <p>
    * Tests the handling of {@code continue} when a loop is expanded.
    * </p>
    */
   public void testLoopBodyBranchClosed() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantLoopBodyBranchClosed/test/LoopBodyBranchClosed.java", 
                "LoopBodyBranchClosed", 
                "deadBody", 
                null,
                "/set/useLoopInvariantLoopBodyBranchClosed/oracle/LoopBodyBranchClosed.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantLoopUsageBranchClosed
    * </p>
    * <p>
    * Tests the handling of {@code continue} when a loop is expanded.
    * </p>
    */
   public void testLoopUsageBranchClosed() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantLoopUsageBranchClosed/test/LoopUsageBranchClosed.java", 
                "LoopUsageBranchClosed", 
                "deadCodeAfterLoop", 
                null,
                "/set/useLoopInvariantLoopUsageBranchClosed/oracle/LoopUsageBranchClosed.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/nestedLoopsWithContinue
    * </p>
    * <p>
    * Tests the handling of {@code continue} when a loop is expanded.
    * </p>
    */
   public void testNestedLoopsWithContinue() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/nestedLoopsWithContinue/test/NestedLoopsWithContinue.java", 
                "NestedLoopsWithContinue", 
                "main", 
                null,
                "/set/nestedLoopsWithContinue/oracle/NestedLoopsWithContinue.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySumWhileWithContinue
    * </p>
    * <p>
    * Tests the handling of {@code continue} when a loop invariant is applied.
    * </p>
    */
   public void testArraySumWhileWithContinue() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySumWhileWithContinue/test/ArraySumWhileWithContinue.java", 
                "ArraySumWhileWithContinue", 
                "sum", 
                null,
                "/set/useLoopInvariantArraySumWhileWithContinue/oracle/ArraySumWhileWithContinue.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantVoidWhileWithReturn
    * </p>
    * <p>
    * Tests the handling of {@code return} when a loop invariant is applied.
    * </p>
    */
   public void testVoidWhileWithReturn() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantVoidWhileWithReturn/test/VoidWhileWithReturn.java", 
                "VoidWhileWithReturn", 
                "sum", 
                null,
                "/set/useLoopInvariantVoidWhileWithReturn/oracle/VoidWhileWithReturn.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySumWhileWithReturn
    * </p>
    * <p>
    * Tests the handling of {@code return} when a loop invariant is applied.
    * </p>
    */
   public void testArraySumWhileWithReturn() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySumWhileWithReturn/test/ArraySumWhileWithReturn.java", 
                "ArraySumWhileWithReturn", 
                "sum", 
                null,
                "/set/useLoopInvariantArraySumWhileWithReturn/oracle/ArraySumWhileWithReturn.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySumWhileWithBreak
    * </p>
    * <p>
    * Tests the handling of {@code break} when a loop invariant is applied.
    * </p>
    */
   public void testArraySumWhileWithBreak() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySumWhileWithBreak/test/ArraySumWhileWithBreak.java", 
                "ArraySumWhileWithBreak", 
                "sum", 
                null,
                "/set/useLoopInvariantArraySumWhileWithBreak/oracle/ArraySumWhileWithBreak.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySumWhileWithException
    * </p>
    * <p>
    * Tests the handling of thrown exceptions when a loop invariant is applied.
    * </p>
    */
   public void testArraySumWhileWithException() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySumWhileWithException/test/ArraySumWhileWithException.java", 
                "ArraySumWhileWithException", 
                "sum", 
                "array != null",
                "/set/useLoopInvariantArraySumWhileWithException/oracle/ArraySumWhileWithException.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantWhileWithMethodCallAsCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsCondition_preMethodContract() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantWhileWithMethodCallAsCondition/test/WhileWithMethodCallAsCondition.java", 
                "WhileWithMethodCallAsCondition", 
                "size", 
                "array != null",
                "/set/useLoopInvariantWhileWithMethodCallAsCondition/oracle/WhileWithMethodCallAsCondition_preMethodContract.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantWhileWithMethodCallAsCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsCondition_preExpandMethods() throws Exception {
      doSETTest(testCaseDirectory,
                "/set/useLoopInvariantWhileWithMethodCallAsCondition/test/WhileWithMethodCallAsCondition.java", 
                "WhileWithMethodCallAsCondition", 
                "size", 
                "array != null",
                "/set/useLoopInvariantWhileWithMethodCallAsCondition/oracle/WhileWithMethodCallAsCondition_preExpandMethods.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantWhileWithMethodCallAsCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsCondition_NoPreMethodContract() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantWhileWithMethodCallAsCondition/test/WhileWithMethodCallAsCondition.java", 
                "WhileWithMethodCallAsCondition", 
                "size", 
                null,
                "/set/useLoopInvariantWhileWithMethodCallAsCondition/oracle/WhileWithMethodCallAsCondition_NoPreMethodContract.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantWhileWithLoopInvariantInCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithLoopInvariantInCondition() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantWhileWithLoopInvariantInCondition/test/WhileWithLoopInvariantInCondition.java", 
                "WhileWithLoopInvariantInCondition", 
                "size", 
                null,
                "/set/useLoopInvariantWhileWithLoopInvariantInCondition/oracle/WhileWithLoopInvariantInCondition.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantWhileWithMethodCallAsConditionOnObject
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsConditionOnObject() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantWhileWithMethodCallAsConditionOnObject/test/WhileWithMethodCallAsConditionOnObject.java", 
                "WhileWithMethodCallAsConditionOnObject", 
                "size", 
                null,
                "/set/useLoopInvariantWhileWithMethodCallAsConditionOnObject/oracle/WhileWithMethodCallAsConditionOnObject.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantWhileWithMethodCallAsCondition
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testWhileWithMethodCallAsCondition_NoPreExpandMethods() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantWhileWithMethodCallAsCondition/test/WhileWithMethodCallAsCondition.java", 
                "WhileWithMethodCallAsCondition", 
                "size", 
                null,
                "/set/useLoopInvariantWhileWithMethodCallAsCondition/oracle/WhileWithMethodCallAsCondition_NoPreExpandMethods.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySizeDoWhile
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySizeDoWhile() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySizeDoWhile/test/ArraySizeDoWhile.java", 
                "ArraySizeDoWhile", 
                "size", 
                "array != null",
                "/set/useLoopInvariantArraySizeDoWhile/oracle/ArraySizeDoWhile.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySizeWhile
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySizeWhile() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySizeWhile/test/ArraySizeWhile.java", 
                "ArraySizeWhile", 
                "size", 
                "array != null",
                "/set/useLoopInvariantArraySizeWhile/oracle/ArraySizeWhile.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySumFor
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySumFor() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySumFor/test/ArraySumFor.java", 
                "ArraySumFor", 
                "sum", 
                "array != null",
                "/set/useLoopInvariantArraySumFor/oracle/ArraySumFor.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySumForEach
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySumForEach() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySumForEach/test/ArraySumForEach.java", 
                "ArraySumForEach", 
                "sum", 
                "array != null",
                "/set/useLoopInvariantArraySumForEach/oracle/ArraySumForEach.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySumWhile
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySumWhile() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySumWhile/test/ArraySumWhile.java", 
                "ArraySumWhile", 
                "sum", 
                "array != null",
                "/set/useLoopInvariantArraySumWhile/oracle/ArraySumWhile.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/useLoopInvariantArraySumWhileInitiallyInvalid
    * </p>
    * <p>
    * The preserves loop body branch is fulfilled and not contained in the symbolic execution tree!
    * </p>
    */
   public void testUseLoopInvariantArraySumWhileInitiallyInvalid() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useLoopInvariantArraySumWhileInitiallyInvalid/test/ArraySumWhileInitiallyInvalid.java", 
                "ArraySumWhileInitiallyInvalid", 
                "sum", 
                "array != null",
                "/set/useLoopInvariantArraySumWhileInitiallyInvalid/oracle/ArraySumWhileInitiallyInvalid.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractQueryTest
    */
   public void testUseOperationContractQueryTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractQueryTest/test/UseOperationContractQueryTest.java", 
                "UseOperationContractQueryTest", 
                "main", 
                "value == magicNumber()",
                "/set/useOperationContractQueryTest/oracle/UseOperationContractQueryTest.xml",
                false,
                false,
                true,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractAllBranchesOpenTest
    */
   public void testUseOperationContractAllBranchesOpenTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractAllBranchesOpenTest/test/UseOperationContractAllBranchesOpenTest.java", 
                "UseOperationContractAllBranchesOpenTest", 
                "main", 
                null,
                "/set/useOperationContractAllBranchesOpenTest/oracle/UseOperationContractAllBranchesOpenTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/identicalTermsDuringProof
    */
   public void testIdenticalTermsDuringProof() throws Exception {
      // Make sure that correct symbolic execution tree is created.
      SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env = doSETTest(testCaseDirectory, 
                                                                               "/set/identicalTermsDuringProof/test/IdenticalTermsDuringProof.java", 
                                                                               "IdenticalTermsDuringProof", 
                                                                               "mid", 
                                                                               null,
                                                                               "/set/identicalTermsDuringProof/oracle/IdenticalTermsDuringProof.xml",
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               ALL_IN_ONE_RUN,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false,
                                                                               false);
      try {
         // Find both statements "mid = y;".
         IExecutionStart startNode = env.getBuilder().getStartNode();
         IExecutionMethodCall methodCall = (IExecutionMethodCall)startNode.getChildren()[0];
         IExecutionStatement intMidZ = (IExecutionStatement)methodCall.getChildren()[0];
         IExecutionBranchStatement ifYZ = (IExecutionBranchStatement)intMidZ.getChildren()[0];
         IExecutionBranchCondition notXY = (IExecutionBranchCondition)ifYZ.getChildren()[0];
         IExecutionBranchStatement ifXZ = (IExecutionBranchStatement)notXY.getChildren()[0];
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
    * Tests example: /set/labelTest
    */
   public void testLabelTest_doubled() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/labelTest/test/LabelTest.java", 
                "LabelTest", 
                "doubled", 
                null,
                "/set/labelTest/oracle/LabelTest_doubled.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/labelTest
    */
   public void testLabelTest_lost() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/labelTest/test/LabelTest.java", 
                "LabelTest", 
                "lost", 
                null,
                "/set/labelTest/oracle/LabelTest_lost.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/emptyBlockTest
    */
   public void testEmptyBlockTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/emptyBlockTest/test/EmptyBlockTest.java", 
                "EmptyBlockTest", 
                "emptyBlocks", 
                null,
                "/set/emptyBlockTest/oracle/EmptyBlockTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractExceptionalNoPreconditionWithNullCheckTest
    */
   public void testUseOperationContractExceptionalNoPreconditionWithNullCheckTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractExceptionalNoPreconditionWithNullCheckTest/test/UseOperationContractExceptionalNoPreconditionWithNullCheckTest.java", 
                "UseOperationContractExceptionalNoPreconditionWithNullCheckTest", 
                "main", 
                null,
                "/set/useOperationContractExceptionalNoPreconditionWithNullCheckTest/oracle/UseOperationContractExceptionalNoPreconditionWithNullCheckTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractFalsePreconditionTest
    */
   public void testUseOperationContractFalsePreconditionTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractFalsePreconditionTest/test/UseOperationContractFalsePreconditionTest.java", 
                "UseOperationContractFalsePreconditionTest", 
                "main", 
                null,
                "/set/useOperationContractFalsePreconditionTest/oracle/UseOperationContractFalsePreconditionTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractFixedNormalPostTest
    */
   public void testUseOperationContractFixedNormalPostTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractFixedNormalPostTest/test/UseOperationContractFixedNormalPostTest.java", 
                "UseOperationContractFixedNormalPostTest", 
                "main", 
                null,
                "/set/useOperationContractFixedNormalPostTest/oracle/UseOperationContractFixedNormalPostTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractInvalidPreconditionOnObjectTest
    */
   public void testUseOperationContractInvalidPreconditionOnObjectTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractInvalidPreconditionOnObjectTest/test/UseOperationContractInvalidPreconditionOnObjectTest.java", 
                "UseOperationContractInvalidPreconditionOnObjectTest", 
                "main", 
                null,
                "/set/useOperationContractInvalidPreconditionOnObjectTest/oracle/UseOperationContractInvalidPreconditionOnObjectTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractInvalidPreconditionTest
    */
   public void testUseOperationContractInvalidPreconditionTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractInvalidPreconditionTest/test/UseOperationContractInvalidPreconditionTest.java", 
                "UseOperationContractInvalidPreconditionTest", 
                "main", 
                null,
                "/set/useOperationContractInvalidPreconditionTest/oracle/UseOperationContractInvalidPreconditionTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractNoExceptionTest
    */
   public void testUseOperationContractNoExceptionTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractNoExceptionTest/test/UseOperationContractNoExceptionTest.java", 
                "UseOperationContractNoExceptionTest", 
                "main", 
                null,
                "/set/useOperationContractNoExceptionTest/oracle/UseOperationContractNoExceptionTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractNoPreconditionTest
    */
   public void testUseOperationContractNoPreconditionTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractNoPreconditionTest/test/UseOperationContractNoPreconditionTest.java", 
                "UseOperationContractNoPreconditionTest", 
                "main", 
                null,
                "/set/useOperationContractNoPreconditionTest/oracle/UseOperationContractNoPreconditionTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractNoPreconditionWithNullCheckTest
    */
   public void testUseOperationContractNoPreconditionWithNullCheckTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractNoPreconditionWithNullCheckTest/test/UseOperationContractNoPreconditionWithNullCheckTest.java", 
                "UseOperationContractNoPreconditionWithNullCheckTest", 
                "main", 
                null,
                "/set/useOperationContractNoPreconditionWithNullCheckTest/oracle/UseOperationContractNoPreconditionWithNullCheckTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractNormalAndExceptionalBranchTest
    */
   public void testUseOperationContractNormalAndExceptionalBranchTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractNormalAndExceptionalBranchTest/test/UseOperationContractNormalAndExceptionalBranchTest.java", 
                "UseOperationContractNormalAndExceptionalBranchTest", 
                "main", 
                null,
                "/set/useOperationContractNormalAndExceptionalBranchTest/oracle/UseOperationContractNormalAndExceptionalBranchTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/useOperationContractNormalAndExceptionalTogetherTest
    */
   public void testUseOperationContractNormalAndExceptionalTogetherTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/useOperationContractNormalAndExceptionalTogetherTest/test/UseOperationContractNormalAndExceptionalTogetherTest.java", 
                "UseOperationContractNormalAndExceptionalTogetherTest", 
                "main", 
                null,
                "/set/useOperationContractNormalAndExceptionalTogetherTest/oracle/UseOperationContractNormalAndExceptionalTogetherTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                true,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/complexConstructorTest
    */
   public void testComplexConstructorTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/complexConstructorTest/test/ComplexConstructorTest.java", 
                "ComplexConstructorTest", 
                "main", 
                null,
                "/set/complexConstructorTest/oracle/ComplexConstructorTest.xml",
                false,
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/simpleConstructorTest
    */
   public void testSimpleConstructorTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/simpleConstructorTest/test/SimpleConstructorTest.java", 
                "SimpleConstructorTest", 
                "main", 
                null,
                "/set/simpleConstructorTest/oracle/SimpleConstructorTest.xml",
                false,
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/variablesUnknownTest
    */
   public void testVariablesUnknownTest() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/variablesUnknownTest/test/UnknownTest.java", 
                          "endless.UnknownTest",
                          "main", 
                          null,
                          "/set/variablesUnknownTest/oracle/UnknownTest.xml",
                          false,
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: /set/variablesParameterAttributesChange
    */
   public void testElseIfTest_variablesParameterAttributesChange() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variablesParameterAttributesChange/test/VariablesParameterAttributesChange.java", 
                "VariablesParameterAttributesChange", 
                "main", 
                null,
                "/set/variablesParameterAttributesChange/oracle/VariablesParameterAttributesChange.xml",
                false,
                true,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/elseIfTest
    */
   public void testElseIfTest_mergedBranchConditions() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/elseIfTest/test/ElseIfTest.java", 
                "ElseIfTest", 
                "elseIf", 
                null,
                "/set/elseIfTest/oracle/ElseIfTestMergedBranchConditions.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                true,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/switchCaseTest
    */
   public void testSwitchCaseTest_mergedBranchConditions() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/switchCaseTest/test/SwitchCaseTest.java", 
                "SwitchCaseTest", 
                "switchCase", 
                null,
                "/set/switchCaseTest/oracle/SwitchCaseTestMergedBranchConditions.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                true,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/loopIterationTest
    */
   public void testLoopIteration_LoopWithMethod() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/loopIterationTest/test/LoopIterationTest.java", 
                "LoopIterationTest", 
                "loopMultipleTimes", 
                null,
                "/set/loopIterationTest/oracle/LoopIterationTest_loopMultipleTimes.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/loopIterationTest
    */
   public void testLoopIteration_LoopStatementCopied() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/loopIterationTest/test/LoopIterationTest.java", 
                "LoopIterationTest", 
                "mainWorks", 
                null,
                "/set/loopIterationTest/oracle/LoopIterationTest_mainWorks.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/loopIterationTest
    */
   public void testLoopIteration_LoopStatementReused() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/loopIterationTest/test/LoopIterationTest.java", 
                "LoopIterationTest", 
                "main", 
                null,
                "/set/loopIterationTest/oracle/LoopIterationTest_main.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/variablesArrayTest
    */
   public void testVariablesArrayTest() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/variablesArrayTest/test/VariablesArrayTest.java", 
                          "VariablesArrayTest", 
                          "main", 
                          null,
                          "/set/variablesArrayTest/oracle/VariablesArrayTest.xml",
                          false,
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: /set/variablesInstanceVariableTest
    */
   public void testVariablesInstanceVariableTest() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/variablesInstanceVariableTest/test/VariablesInstanceVariableTest.java", 
                          "VariablesInstanceVariableTest", 
                          "main", 
                          null,
                          "/set/variablesInstanceVariableTest/oracle/VariablesInstanceVariableTest.xml",
                          false,
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: /set/variablesLocalTest
    */
   public void testVariablesLocalTest() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/variablesLocalTest/test/VariablesLocalTest.java", 
                          "VariablesLocalTest", 
                          "main", 
                          null,
                          "/set/variablesLocalTest/oracle/VariablesLocalTest.xml",
                          false,
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: /set/variablesStaticTest
    */
   public void testVariablesStaticTest() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/variablesStaticTest/test/VariablesStaticTest.java", 
                          "VariablesStaticTest", 
                          "main", 
                          null,
                          "/set/variablesStaticTest/oracle/VariablesStaticTest.xml",
                          false,
                          true,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: /set/complexFlatSteps
    */
   public void testComplexFlatSteps() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/complexFlatSteps/test/ComplexFlatSteps.java", 
                "ComplexFlatSteps", 
                "doSomething", 
                null,
                "/set/complexFlatSteps/oracle/ComplexFlatSteps.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/complexIf
    */
   public void testComplexIf() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/complexIf/test/ComplexIf.java", 
                "ComplexIf", 
                "min", 
                null,
                "/set/complexIf/oracle/ComplexIf.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/doWhileFalseTest
    */
   public void testDoWhileFlaseTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/doWhileFalseTest/test/DoWhileFalseTest.java", 
                "DoWhileFalseTest", 
                "main", 
                null,
                "/set/doWhileFalseTest/oracle/DoWhileFalseTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/doWhileTest
    */
   public void testDoWhileTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/doWhileTest/test/DoWhileTest.java", 
                "DoWhileTest", 
                "main", 
                null,
                "/set/doWhileTest/oracle/DoWhileTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/elseIfDifferentVariables
    */
   public void testElseIfDifferentVariables() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/elseIfDifferentVariables/test/ElseIfDifferentVariables.java", 
                "ElseIfDifferentVariables", 
                "main", 
                null,
                "/set/elseIfDifferentVariables/oracle/ElseIfDifferentVariables.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/elseIfTest
    */
   public void testElseIfTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/elseIfTest/test/ElseIfTest.java", 
                "ElseIfTest", 
                "elseIf", 
                null,
                "/set/elseIfTest/oracle/ElseIfTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/fixedRecursiveMethodCallTest
    */
   public void testFixedRecursiveMethodCallTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/fixedRecursiveMethodCallTest/test/FixedRecursiveMethodCallTest.java", 
                "FixedRecursiveMethodCallTest", 
                "decreaseValue", 
                null,
                "/set/fixedRecursiveMethodCallTest/oracle/FixedRecursiveMethodCallTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/forEachTest
    */
   public void testForEachTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/forEachTest/test/ForEachTest.java", 
                "ForEachTest", 
                "main", 
                null,
                "/set/forEachTest/oracle/ForEachTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/forFalseTest
    */
   public void testForFalseTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/forFalseTest/test/ForFalseTest.java", 
                "ForFalseTest", 
                "main", 
                null,
                "/set/forFalseTest/oracle/ForFalseTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/forTest
    */
   public void testForTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/forTest/test/ForTest.java", 
                "ForTest", 
                "main", 
                null,
                "/set/forTest/oracle/ForTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/functionalDoWhileTest
    */
   public void testFunctionalDoWhileTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/functionalDoWhileTest/test/FunctionalDoWhileTest.java", 
                "FunctionalDoWhileTest", 
                "main", 
                null,
                "/set/functionalDoWhileTest/oracle/FunctionalDoWhileTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/functionalForTest
    */
   public void testFunctionalForTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/functionalForTest/test/FunctionalForTest.java", 
                "FunctionalForTest", 
                "main", 
                null,
                "/set/functionalForTest/oracle/FunctionalForTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/functionalIf
    */
   public void testFunctionalIf() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/functionalIf/test/FunctionalIf.java", 
                "FunctionalIf", 
                "min", 
                null,
                "/set/functionalIf/oracle/FunctionalIf.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/functionalWhileTest
    */
   public void testFunctionalWhileTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/functionalWhileTest/test/FunctionalWhileTest.java", 
                "FunctionalWhileTest", 
                "main", 
                null,
                "/set/functionalWhileTest/oracle/FunctionalWhileTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/methodCallOnObject
    */
   public void testMethodCallOnObject() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/methodCallOnObject/test/MethodCallOnObject.java", 
                "MethodCallOnObject", 
                "main", 
                null,
                "/set/methodCallOnObject/oracle/MethodCallOnObject.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/methodCallOnObjectWithException
    */
   public void testMethodCallOnObjectWithException() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/methodCallOnObjectWithException/test/MethodCallOnObjectWithException.java", 
                "MethodCallOnObjectWithException", 
                "main", 
                null,
                "/set/methodCallOnObjectWithException/oracle/MethodCallOnObjectWithException.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/methodCallParallelTest
    */
   public void testMethodCallParallelTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/methodCallParallelTest/test/MethodCallParallelTest.java", 
                "MethodCallParallelTest", 
                "main", 
                null,
                "/set/methodCallParallelTest/oracle/MethodCallParallelTest.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/methodFormatTest
    */
   public void testMethodFormatTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/methodFormatTest/test/MethodFormatTest.java", 
                "MethodFormatTest", 
                "main", 
                null,
                "/set/methodFormatTest/oracle/MethodFormatTest.xml",
                false,
                false,
                false,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/methodHierarchyCallTest
    */
   public void testMethodHierarchyCallTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/methodHierarchyCallTest/test/MethodHierarchyCallTest.java", 
                "MethodHierarchyCallTest", 
                "main", 
                null,
                "/set/methodHierarchyCallTest/oracle/MethodHierarchyCallTest.xml",
                false,
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/methodHierarchyCallWithExceptionTest
    */
   public void testMethodHierarchyCallWithExceptionTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/methodHierarchyCallWithExceptionTest/test/MethodHierarchyCallWithExceptionTest.java", 
                "MethodHierarchyCallWithExceptionTest", 
                "main", 
                null,
                "/set/methodHierarchyCallWithExceptionTest/oracle/MethodHierarchyCallWithExceptionTest.xml",
                false,
                false,
                true,
                true,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/nestedDoWhileTest
    */
   public void testNestedDoWhileTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/nestedDoWhileTest/test/NestedDoWhileTest.java", 
                "NestedDoWhileTest", 
                "main", 
                null,
                "/set/nestedDoWhileTest/oracle/NestedDoWhileTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/nestedForTest
    */
   public void testNestedForTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/nestedForTest/test/NestedForTest.java", 
                "NestedForTest", 
                "main", 
                null,
                "/set/nestedForTest/oracle/NestedForTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/nestedWhileTest
    */
   public void testNestedWhileTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/nestedWhileTest/test/NestedWhileTest.java", 
                "NestedWhileTest", 
                "mainNested", 
                 null,
                "/set/nestedWhileTest/oracle/NestedWhileTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * <p>
    * Tests example: /set/recursiveFibonacci
    * </p>
    * <p>
    * This test produces a deep symbolic execution tree to make sure
    * that no {@link StackOverflowError}s are thrown.
    * </p>
    */
   public void testRecursiveFibonacci_LONG_RUNNING_TEST() throws Exception {
      doSETTestAndDispose(testCaseDirectory, 
                          "/set/recursiveFibonacci/test/RecursiveFibonacci.java", 
                          "RecursiveFibonacci", 
                          "fibonacci10", 
                          null,
                          "/set/recursiveFibonacci/oracle/RecursiveFibonacci.xml",
                          false,
                          false,
                          false,
                          false,
                          ALL_IN_ONE_RUN,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false,
                          false);
   }
   
   /**
    * Tests example: /set/simpleIf
    */
   public void testSimpleIf() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/simpleIf/test/SimpleIf.java", 
                "SimpleIf", 
                "min", 
                null,
                "/set/simpleIf/oracle/SimpleIf.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/simpleNullPointerSplitTest
    */
   public void testSimpleNullPointerSplitTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/simpleNullPointerSplitTest/test/SimpleNullPointerSplitTest.java", 
                "SimpleNullPointerSplitTest", 
                "main", 
                null,
                "/set/simpleNullPointerSplitTest/oracle/SimpleNullPointerSplitTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/statementKindTest
    */
   public void testStatementKindTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/statementKindTest/test/StatementKindTest.java", 
                "StatementKindTest", 
                "main", 
                null,
                "/set/statementKindTest/oracle/StatementKindTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/statements
    */
   public void testStatements() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/statements/test/FlatSteps.java", 
                "FlatSteps", 
                "doSomething", 
                null,
                "/set/statements/oracle/FlatSteps.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/staticMethodCall
    */
   public void testStaticMethodCall() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/staticMethodCall/test/StaticMethodCall.java", 
                "StaticMethodCall", 
                "main", 
                null,
                "/set/staticMethodCall/oracle/StaticMethodCall.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/switchCaseTest
    */
   public void testSwitchCaseTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/switchCaseTest/test/SwitchCaseTest.java", 
                "SwitchCaseTest", 
                "switchCase", 
                null,
                "/set/switchCaseTest/oracle/SwitchCaseTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/throwTest
    */
   public void testThrowTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/throwTest/test/ThrowTest.java", 
                "ThrowTest", 
                "main", 
                null,
                "/set/throwTest/oracle/ThrowTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/throwVariableTest
    */
   public void testThrowVariableTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/throwVariableTest/test/ThrowVariableTest.java", 
                "ThrowVariableTest", 
                "main", 
                null,
                "/set/throwVariableTest/oracle/ThrowVariableTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/tryCatchFinally
    */
   public void testTryCatchFinally() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/tryCatchFinally/test/TryCatchFinally.java", 
                "TryCatchFinally", 
                "tryCatchFinally", 
                null,
                "/set/tryCatchFinally/oracle/TryCatchFinally.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/whileFalseTest
    */
   public void testWhileFalseTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/whileFalseTest/test/WhileFalseTest.java", 
                "WhileFalseTest", 
                "main", 
                null,
                "/set/whileFalseTest/oracle/WhileFalseTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
   
   /**
    * Tests example: /set/whileTest
    */
   public void testWhileTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/whileTest/test/WhileTest.java", 
                "WhileTest", 
                "main", 
                null,
                "/set/whileTest/oracle/WhileTest.xml",
                false,
                false,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                false,
                false,
                false,
                false,
                false,
                false);
   }
}