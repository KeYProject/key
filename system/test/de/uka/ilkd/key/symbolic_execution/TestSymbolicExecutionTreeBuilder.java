package de.uka.ilkd.key.symbolic_execution;

import java.io.File;
import java.io.IOException;
import java.util.Map;

import javax.xml.parsers.ParserConfigurationException;

import org.xml.sax.SAXException;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;

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
    * Number of executed SET nodes to execute all in one.
    */
   private static final int ALL_IN_ONE_RUN = ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_IN_COMPLETE_RUN;

   /**
    * Number of executed SET nodes for only one SET node per auto mode run.
    */
   private static final int SINGLE_SET_NODE_RUN = ExecutedSymbolicExecutionTreeNodesStopCondition.MAXIMAL_NUMBER_OF_SET_NODES_TO_EXECUTE_PER_GOAL_FOR_ONE_STEP;

   /**
    * Default stop conditions of executed SET nodes.
    */
   private static final int[] DEFAULT_MAXIMAL_SET_NODES_PER_RUN = {ALL_IN_ONE_RUN, SINGLE_SET_NODE_RUN};
   
   /**
    * Tests example: examples/_testcase/set/loopIterationTest
    */
   public void testLoopIteration_LoopWithMethod() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/loopIterationTest/test/LoopIterationTest.java", 
             "LoopIterationTest", 
             "loopMultipleTimes", 
             "examples/_testcase/set/loopIterationTest/oracle/LoopIterationTest_loopMultipleTimes.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/loopIterationTest
    */
   public void testLoopIteration_LoopStatementCopied() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/loopIterationTest/test/LoopIterationTest.java", 
             "LoopIterationTest", 
             "mainWorks", 
             "examples/_testcase/set/loopIterationTest/oracle/LoopIterationTest_mainWorks.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/loopIterationTest
    */
   public void testLoopIteration_LoopStatementReused() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/loopIterationTest/test/LoopIterationTest.java", 
             "LoopIterationTest", 
             "main", 
             "examples/_testcase/set/loopIterationTest/oracle/LoopIterationTest_main.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesArrayTest
    */
   public void testVariablesArrayTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/variablesArrayTest/test/VariablesArrayTest.java", 
             "VariablesArrayTest", 
             "main", 
             "examples/_testcase/set/variablesArrayTest/oracle/VariablesArrayTest.xml",
             true,
             ALL_IN_ONE_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesInstanceVariableTest
    */
   public void testVariablesInstanceVariableTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/variablesInstanceVariableTest/test/VariablesInstanceVariableTest.java", 
             "VariablesInstanceVariableTest", 
             "main", 
             "examples/_testcase/set/variablesInstanceVariableTest/oracle/VariablesInstanceVariableTest.xml",
             true,
             ALL_IN_ONE_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesLocalTest
    */
   public void testVariablesLocalTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/variablesLocalTest/test/VariablesLocalTest.java", 
             "VariablesLocalTest", 
             "main", 
             "examples/_testcase/set/variablesLocalTest/oracle/VariablesLocalTest.xml",
             true,
             ALL_IN_ONE_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesStaticTest
    */
   public void testVariablesStaticTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/variablesStaticTest/test/VariablesStaticTest.java", 
             "VariablesStaticTest", 
             "main", 
             "examples/_testcase/set/variablesStaticTest/oracle/VariablesStaticTest.xml",
             true,
             ALL_IN_ONE_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexFlatSteps
    */
   public void testComplexFlatSteps() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/complexFlatSteps/test/ComplexFlatSteps.java", 
             "ComplexFlatSteps", 
             "doSomething", 
             "examples/_testcase/set/complexFlatSteps/oracle/ComplexFlatSteps.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/complexIf
    */
   public void testComplexIf() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/complexIf/test/ComplexIf.java", 
             "ComplexIf", 
             "min", 
             "examples/_testcase/set/complexIf/oracle/ComplexIf.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/doWhileFalseTest
    */
   public void testDoWhileFlaseTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/doWhileFalseTest/test/DoWhileFalseTest.java", 
             "DoWhileFalseTest", 
             "main", 
             "examples/_testcase/set/doWhileFalseTest/oracle/DoWhileFalseTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/doWhileTest
    */
   public void testDoWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/doWhileTest/test/DoWhileTest.java", 
             "DoWhileTest", 
             "main", 
             "examples/_testcase/set/doWhileTest/oracle/DoWhileTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfDifferentVariables
    */
   public void testElseIfDifferentVariables() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/elseIfDifferentVariables/test/ElseIfDifferentVariables.java", 
             "ElseIfDifferentVariables", 
             "main", 
             "examples/_testcase/set/elseIfDifferentVariables/oracle/ElseIfDifferentVariables.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/elseIfTest
    */
   public void testElseIfTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/elseIfTest/test/ElseIfTest.java", 
             "ElseIfTest", 
             "elseIf", 
             "examples/_testcase/set/elseIfTest/oracle/ElseIfTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/fixedRecursiveMethodCallTest
    */
   public void testFixedRecursiveMethodCallTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/fixedRecursiveMethodCallTest/test/FixedRecursiveMethodCallTest.java", 
             "FixedRecursiveMethodCallTest", 
             "decreaseValue", 
             "examples/_testcase/set/fixedRecursiveMethodCallTest/oracle/FixedRecursiveMethodCallTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/forEachTest
    */
   public void testForEachTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/forEachTest/test/ForEachTest.java", 
             "ForEachTest", 
             "main", 
             "examples/_testcase/set/forEachTest/oracle/ForEachTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/forFalseTest
    */
   public void testForFalseTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/forFalseTest/test/ForFalseTest.java", 
             "ForFalseTest", 
             "main", 
             "examples/_testcase/set/forFalseTest/oracle/ForFalseTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/forTest
    */
   public void testForTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/forTest/test/ForTest.java", 
             "ForTest", 
             "main", 
             "examples/_testcase/set/forTest/oracle/ForTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalDoWhileTest
    */
   public void testFunctionalDoWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/functionalDoWhileTest/test/FunctionalDoWhileTest.java", 
             "FunctionalDoWhileTest", 
             "main", 
             "examples/_testcase/set/functionalDoWhileTest/oracle/FunctionalDoWhileTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalForTest
    */
   public void testFunctionalForTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/functionalForTest/test/FunctionalForTest.java", 
             "FunctionalForTest", 
             "main", 
             "examples/_testcase/set/functionalForTest/oracle/FunctionalForTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalIf
    */
   public void testFunctionalIf() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/functionalIf/test/FunctionalIf.java", 
             "FunctionalIf", 
             "min", 
             "examples/_testcase/set/functionalIf/oracle/FunctionalIf.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/functionalWhileTest
    */
   public void testFunctionalWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/functionalWhileTest/test/FunctionalWhileTest.java", 
             "FunctionalWhileTest", 
             "main", 
             "examples/_testcase/set/functionalWhileTest/oracle/FunctionalWhileTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallOnObject
    */
   public void testMethodCallOnObject() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodCallOnObject/test/MethodCallOnObject.java", 
             "MethodCallOnObject", 
             "main", 
             "examples/_testcase/set/methodCallOnObject/oracle/MethodCallOnObject.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallOnObjectWithException
    */
   public void testMethodCallOnObjectWithException() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodCallOnObjectWithException/test/MethodCallOnObjectWithException.java", 
             "MethodCallOnObjectWithException", 
             "main", 
             "examples/_testcase/set/methodCallOnObjectWithException/oracle/MethodCallOnObjectWithException.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodCallParallelTest
    */
   public void testMethodCallParallelTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodCallParallelTest/test/MethodCallParallelTest.java", 
             "MethodCallParallelTest", 
             "main", 
             "examples/_testcase/set/methodCallParallelTest/oracle/MethodCallParallelTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodFormatTest
    */
   public void testMethodFormatTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodFormatTest/test/MethodFormatTest.java", 
             "MethodFormatTest", 
             "main", 
             "examples/_testcase/set/methodFormatTest/oracle/MethodFormatTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodHierarchyCallTest
    */
   public void testMethodHierarchyCallTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodHierarchyCallTest/test/MethodHierarchyCallTest.java", 
             "MethodHierarchyCallTest", 
             "main", 
             "examples/_testcase/set/methodHierarchyCallTest/oracle/MethodHierarchyCallTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/methodHierarchyCallWithExceptionTest
    */
   public void testMethodHierarchyCallWithExceptionTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/methodHierarchyCallWithExceptionTest/test/MethodHierarchyCallWithExceptionTest.java", 
             "MethodHierarchyCallWithExceptionTest", 
             "main", 
             "examples/_testcase/set/methodHierarchyCallWithExceptionTest/oracle/MethodHierarchyCallWithExceptionTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedDoWhileTest
    */
   public void testNestedDoWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/nestedDoWhileTest/test/NestedDoWhileTest.java", 
             "NestedDoWhileTest", 
             "main", 
             "examples/_testcase/set/nestedDoWhileTest/oracle/NestedDoWhileTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedForTest
    */
   public void testNestedForTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/nestedForTest/test/NestedForTest.java", 
             "NestedForTest", 
             "main", 
             "examples/_testcase/set/nestedForTest/oracle/NestedForTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/nestedWhileTest
    */
   public void testNestedWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/nestedWhileTest/test/NestedWhileTest.java", 
             "NestedWhileTest", 
             "mainNested", 
             "examples/_testcase/set/nestedWhileTest/oracle/NestedWhileTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
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
      doTest(keyRepDirectory, 
             "examples/_testcase/set/recursiveFibonacci/test/RecursiveFibonacci.java", 
             "RecursiveFibonacci", 
             "fibonacci10", 
             "examples/_testcase/set/recursiveFibonacci/oracle/RecursiveFibonacci.xml",
             false,
             ALL_IN_ONE_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleIf
    */
   public void testSimpleIf() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/simpleIf/test/SimpleIf.java", 
             "SimpleIf", 
             "min", 
             "examples/_testcase/set/simpleIf/oracle/SimpleIf.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/simpleNullPointerSplitTest
    */
   public void testSimpleNullPointerSplitTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/simpleNullPointerSplitTest/test/SimpleNullPointerSplitTest.java", 
             "SimpleNullPointerSplitTest", 
             "main", 
             "examples/_testcase/set/simpleNullPointerSplitTest/oracle/SimpleNullPointerSplitTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/statementKindTest
    */
   public void testStatementKindTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/statementKindTest/test/StatementKindTest.java", 
             "StatementKindTest", 
             "main", 
             "examples/_testcase/set/statementKindTest/oracle/StatementKindTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/statements
    */
   public void testStatements() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/statements/test/FlatSteps.java", 
             "FlatSteps", 
             "doSomething", 
             "examples/_testcase/set/statements/oracle/FlatSteps.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/staticMethodCall
    */
   public void testStaticMethodCall() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/staticMethodCall/test/StaticMethodCall.java", 
             "StaticMethodCall", 
             "main", 
             "examples/_testcase/set/staticMethodCall/oracle/StaticMethodCall.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/switchCaseTest
    */
   public void testSwitchCaseTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/switchCaseTest/test/SwitchCaseTest.java", 
             "SwitchCaseTest", 
             "switchCase", 
             "examples/_testcase/set/switchCaseTest/oracle/SwitchCaseTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/throwTest
    */
   public void testThrowTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/throwTest/test/ThrowTest.java", 
             "ThrowTest", 
             "main", 
             "examples/_testcase/set/throwTest/oracle/ThrowTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/throwVariableTest
    */
   public void testThrowVariableTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/throwVariableTest/test/ThrowVariableTest.java", 
             "ThrowVariableTest", 
             "main", 
             "examples/_testcase/set/throwVariableTest/oracle/ThrowVariableTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/tryCatchFinally
    */
   public void testTryCatchFinally() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/tryCatchFinally/test/TryCatchFinally.java", 
             "TryCatchFinally", 
             "tryCatchFinally", 
             "examples/_testcase/set/tryCatchFinally/oracle/TryCatchFinally.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/whileFalseTest
    */
   public void testWhileFalseTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/whileFalseTest/test/WhileFalseTest.java", 
             "WhileFalseTest", 
             "main", 
             "examples/_testcase/set/whileFalseTest/oracle/WhileFalseTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Tests example: examples/_testcase/set/whileTest
    */
   public void testWhileTest() throws Exception {
      doTest(keyRepDirectory, 
             "examples/_testcase/set/whileTest/test/WhileTest.java", 
             "WhileTest", 
             "main", 
             "examples/_testcase/set/whileTest/oracle/WhileTest.xml",
             false,
             DEFAULT_MAXIMAL_SET_NODES_PER_RUN);
   }
   
   /**
    * Executes a test with the following steps:
    * <ol>
    *    <li>Load java file</li>
    *    <li>Instantiate proof for method in container type</li>
    *    <li>Try to close proof in auto mode</li>
    *    <li>Create symbolic execution tree</li>
    *    <li>Create new oracle file in temporary directory {@link #tempNewOracleDirectory} if it is defined</li>
    *    <li>Load oracle file</li>
    *    <li>Compare created symbolic execution tree with oracle model</li>
    * </ol>
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The java class to test.
    * @param methodFullName The method to test.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param includeVariables Include variables?
    * @param maximalNumberOfExecutedSetNodesPerRun The number of executed set nodes per auto mode run. The whole test is executed for each defined value.
    * @throws ProofInputException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected void doTest(File baseDir,
                         String javaPathInBaseDir,
                         String containerTypeName,
                         final String methodFullName,
                         String oraclePathInBaseDirFile,
                         boolean includeVariables,
                         int[] maximalNumberOfExecutedSetNodesPerRun) throws ProofInputException, IOException, ParserConfigurationException, SAXException {
      assertNotNull(maximalNumberOfExecutedSetNodesPerRun);
      for (int i = 0; i < maximalNumberOfExecutedSetNodesPerRun.length; i++) {
         doTest(baseDir, 
                javaPathInBaseDir, 
                containerTypeName, 
                methodFullName, 
                oraclePathInBaseDirFile, 
                includeVariables, 
                maximalNumberOfExecutedSetNodesPerRun[i]);
      }
   }
   
   /**
    * Executes a test with the following steps:
    * <ol>
    *    <li>Load java file</li>
    *    <li>Instantiate proof for method in container type</li>
    *    <li>Try to close proof in auto mode</li>
    *    <li>Create symbolic execution tree</li>
    *    <li>Create new oracle file in temporary directory {@link #tempNewOracleDirectory} if it is defined</li>
    *    <li>Load oracle file</li>
    *    <li>Compare created symbolic execution tree with oracle model</li>
    * </ol>
    * @param baseDir The base directory which contains test and oracle file.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param containerTypeName The java class to test.
    * @param methodFullName The method to test.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param includeVariables Include variables?
    * @param maximalNumberOfExecutedSetNodes The number of executed set nodes per auto mode run.
    * @throws ProofInputException Occurred Exception
    * @throws IOException Occurred Exception
    * @throws ParserConfigurationException Occurred Exception
    * @throws SAXException Occurred Exception
    */
   protected void doTest(File baseDir,
                         String javaPathInBaseDir,
                         String containerTypeName,
                         final String methodFullName,
                         String oraclePathInBaseDirFile,
                         boolean includeVariables,
                         int maximalNumberOfExecutedSetNodes) throws ProofInputException, IOException, ParserConfigurationException, SAXException {
      // Make sure that parameter are valid.
      assertNotNull(javaPathInBaseDir);
      assertNotNull(containerTypeName);
      assertNotNull(methodFullName);
      assertNotNull(oraclePathInBaseDirFile);
      File oracleFile = new File(baseDir, oraclePathInBaseDirFile);
      if (!CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
         assertTrue("Oracle file does not exist. Set \"CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY\" to true to create an oracle file.", oracleFile.exists());
      }
      assertTrue(maximalNumberOfExecutedSetNodes >= 1);
      // Create proof environment for symbolic execution
      SymbolicExecutionEnvironment env = createSymbolicExecutionEnvironment(baseDir, javaPathInBaseDir, containerTypeName, methodFullName);
      // Set stop condition to stop after a number of detected symbolic execution tree nodes instead of applied rules
      ExecutedSymbolicExecutionTreeNodesStopCondition stopCondition = new ExecutedSymbolicExecutionTreeNodesStopCondition(maximalNumberOfExecutedSetNodes);
      env.getProof().getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(stopCondition);
      // Execute auto mode until no more symbolic execution tree nodes are found
      do {
         // Run proof
         env.getUi().startAndWaitForProof(env.getProof());
         // Update symbolic execution tree 
         env.getBuilder().analyse();
         // Make sure that not to many set nodes are executed
         Map<Goal, Integer> executedSetNodesPerGoal = stopCondition.getExectuedSetNodesPerGoal();
         for (Integer value : executedSetNodesPerGoal.values()) {
            assertNotNull(value);
            assertTrue(value.intValue() + " is not less equal to " + maximalNumberOfExecutedSetNodes, value.intValue() <= maximalNumberOfExecutedSetNodes);
         }
      } while(stopCondition.wasSetNodeExecuted());
      // Create new oracle file if required in a temporary directory
      createOracleFile(env.getBuilder().getStartNode(), oraclePathInBaseDirFile, includeVariables);
      // Read oracle file
      ExecutionNodeReader reader = new ExecutionNodeReader();
      IExecutionNode oracleRoot = reader.read(oracleFile);
      assertNotNull(oracleRoot);
      // Make sure that the created symbolic execution tree matches the expected one.
      assertExecutionNodes(oracleRoot, env.getBuilder().getStartNode(), includeVariables, false);
   }
}
