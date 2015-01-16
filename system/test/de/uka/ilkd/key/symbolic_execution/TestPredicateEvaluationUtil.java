package de.uka.ilkd.key.symbolic_execution;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.logic.label.PredicateTermLabel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.BranchResult;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.IPredicateInstruction;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.PredicateEvaluationResult;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.PredicateResult;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.PredicateValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Tests for {@link PredicateEvaluationUtil}.
 * @author Martin Hentschel
 */
public class TestPredicateEvaluationUtil extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests example: examples/_testcase/set/predicateEquivExample
    */
   public void testEquivExample_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedBranchResult goal79 = new ExpectedBranchResult(new ExpectedPredicateResult("2.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.TRUE));
      ExpectedBranchResult goal91 = new ExpectedBranchResult(new ExpectedPredicateResult("2.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.TRUE));
      ExpectedBranchResult goal95 = new ExpectedBranchResult(new ExpectedPredicateResult("2.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.TRUE));
      ExpectedBranchResult goal97 = new ExpectedBranchResult(new ExpectedPredicateResult("5.0", PredicateValue.FALSE)); // SETAccumulate is false
      ExpectedPredicateEvaluationResult result = new ExpectedPredicateEvaluationResult(goal79, goal91, goal95, goal97);
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateEquivExample/test/EquivExampleNoOneStepSimplification.proof", 
                                "examples/_testcase/set/predicateEquivExample/oracle/EquivExample.xml",
                                false,
                                true,
                                result);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateEquivExample
    */
   public void testEquivExample() throws Exception {
      // Create expected results
      ExpectedBranchResult goal39 = new ExpectedBranchResult(new ExpectedPredicateResult("2.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.TRUE));
      ExpectedBranchResult goal50 = new ExpectedBranchResult(new ExpectedPredicateResult("1.0", PredicateValue.FALSE), new ExpectedPredicateResult("2.0", PredicateValue.UNKNOWN), new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.UNKNOWN), new ExpectedPredicateResult("5.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", PredicateValue.UNKNOWN));
      ExpectedBranchResult goal53 = new ExpectedBranchResult(new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("2.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.TRUE), new ExpectedPredicateResult("5.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", PredicateValue.TRUE));
      ExpectedBranchResult goal55 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", PredicateValue.FALSE), new ExpectedPredicateResult("4.0", PredicateValue.UNKNOWN), new ExpectedPredicateResult("5.0", PredicateValue.FALSE)); // SETAccumulate is false
      ExpectedPredicateEvaluationResult result = new ExpectedPredicateEvaluationResult(goal39, goal50, goal53, goal55);
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateEquivExample/test/EquivExample.proof", 
                                "examples/_testcase/set/predicateEquivExample/oracle/EquivExample.xml",
                                false,
                                false,
                                result);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateIfThenElseIntegerTest
    */
   public void testIfThenElseInteger() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult thenResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult elseResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateIfThenElseIntegerTest/test/IfThenElseIntegerTest.java", 
                                "IfThenElseIntegerTest[IfThenElseIntegerTest::magic(int,int)].JML normal_behavior operation contract.0", 
                                "examples/_testcase/set/predicateIfThenElseIntegerTest/oracle/IfThenElseIntegerTest.xml",
                                false,
                                false,
                                thenResult,
                                elseResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateIfThenElseNotFormulaTest
    */
   public void testIfThenElseNotFormula() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult thenResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult elseResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateIfThenElseNotFormulaTest/test/IfThenElseNotFormulaTest.java", 
                                "IfThenElseNotFormulaTest[IfThenElseNotFormulaTest::magic(int,int)].JML normal_behavior operation contract.0", 
                                "examples/_testcase/set/predicateIfThenElseNotFormulaTest/oracle/IfThenElseNotFormulaTest.xml",
                                false,
                                false,
                                thenResult,
                                elseResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateIfThenElseFormulaTest
    */
   public void testIfThenElseFormula() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult thenResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("4.0", PredicateValue.TRUE), new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult elseResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("4.0", PredicateValue.TRUE), new ExpectedPredicateResult("0.0", PredicateValue.FALSE), new ExpectedPredicateResult("2.0", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateIfThenElseFormulaTest/test/IfThenElseFormulaTest.java", 
                                "IfThenElseFormulaTest[IfThenElseFormulaTest::magic(int,int)].JML normal_behavior operation contract.0", 
                                "examples/_testcase/set/predicateIfThenElseFormulaTest/oracle/IfThenElseFormulaTest.xml",
                                false,
                                false,
                                thenResult,
                                elseResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateNotLastEvaluationGivesTruthValue
    */
   public void testNotLastEvaluationGivesTruthValue() throws Exception {
      // Create expected results
      ExpectedBranchResult goal53 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.TRUE), new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.12", PredicateValue.FALSE), new ExpectedPredicateResult("1.13", PredicateValue.TRUE));
      ExpectedBranchResult goal41 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", null), new ExpectedPredicateResult("4.0", null), new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("8.0", null));
      ExpectedBranchResult goal39 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", null), new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("8.0",  null));
      ExpectedBranchResult goal55 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", null), new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.11", PredicateValue.TRUE));
      ExpectedPredicateEvaluationResult result = new ExpectedPredicateEvaluationResult(goal53, goal41, goal39, goal55);
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateNotLastEvaluationGivesTruthValue/test/NotLastEvaluationGivesTruthValue.proof", 
                                "examples/_testcase/set/predicateNotLastEvaluationGivesTruthValue/oracle/NotLastEvaluationGivesTruthValue.xml",
                                false,
                                true,
                                result);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateArraySumWhile
    */
   public void testArraySumWhile_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult initialResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("14.0", PredicateValue.TRUE), new ExpectedPredicateResult("15.0", PredicateValue.TRUE), new ExpectedPredicateResult("16.0", PredicateValue.TRUE), new ExpectedPredicateResult("17.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult preservesResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("18.0", PredicateValue.TRUE), new ExpectedPredicateResult("19.0", PredicateValue.TRUE), new ExpectedPredicateResult("20.0", PredicateValue.TRUE), new ExpectedPredicateResult("21.0", PredicateValue.TRUE), new ExpectedPredicateResult("22.0", PredicateValue.TRUE), new ExpectedPredicateResult("23.0", PredicateValue.TRUE), new ExpectedPredicateResult("24.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("2.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.FALSE), new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("9.0", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateArraySumWhile/test/ArraySumWhileNoOneStepSimplification.proof", 
                                "examples/_testcase/set/predicateArraySumWhile/oracle/ArraySumWhile.xml",
                                false,
                                true,
                                initialResult,
                                preservesResult,
                                terminationResult);
   }
   
// TODO: Make test working by fixing One Step Simplification
//   /**
//    * Tests example: examples/_testcase/set/predicateArraySumWhile
//    */
//   public void testArraySumWhile() throws Exception {
//      // Create expected results
//      ExpectedPredicateEvaluationResult initialResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("14.0", PredicateValue.TRUE), new ExpectedPredicateResult("15.0", PredicateValue.TRUE), new ExpectedPredicateResult("16.0", PredicateValue.TRUE), new ExpectedPredicateResult("17.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult preservesResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("18.0", PredicateValue.TRUE), new ExpectedPredicateResult("19.0", PredicateValue.TRUE), new ExpectedPredicateResult("20.0", PredicateValue.TRUE), new ExpectedPredicateResult("21.0", PredicateValue.TRUE), new ExpectedPredicateResult("22.0", PredicateValue.TRUE), new ExpectedPredicateResult("23.0", PredicateValue.TRUE), new ExpectedPredicateResult("24.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("2.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.FALSE), new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("9.0", PredicateValue.TRUE)));
//      // Perform test
//      doPredicateEvaluationTest("examples/_testcase/set/predicateArraySumWhile/test/ArraySumWhile.proof", 
//                                "examples/_testcase/set/predicateArraySumWhile/oracle/ArraySumWhile.xml",
//                                false,
//                                true,
//                                initialResult,
//                                preservesResult,
//                                terminationResult);
//   }
   
   /**
    * Tests example: examples/_testcase/set/predicateArrayUtil
    */
   public void testArrayUtil_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult goal97 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("5.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult goal826 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("17.0", PredicateValue.TRUE), new ExpectedPredicateResult("18.0", PredicateValue.TRUE), new ExpectedPredicateResult("20.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult goal630 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("13.0", PredicateValue.FALSE)));
      ExpectedPredicateEvaluationResult goal792 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("9.0", PredicateValue.TRUE), new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.0", PredicateValue.TRUE), new ExpectedPredicateResult("12.0", PredicateValue.TRUE), new ExpectedPredicateResult("13.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult goal1024 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult goal1161 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateArrayUtil/test/ArrayUtilNoOneStepSimplification.proof", 
                                "examples/_testcase/set/predicateArrayUtil/oracle/ArrayUtil.xml",
                                true,
                                true,
                                goal97,
                                goal826,
                                goal630,
                                goal792,
                                goal1024,
                                goal1161);
   }
   
// TODO: Make test working by fixing One Step Simplification
//   /**
//    * Tests example: examples/_testcase/set/predicateArrayUtil
//    */
//   public void testArrayUtil() throws Exception {
//      // Create expected results
//      ExpectedPredicateEvaluationResult goal97 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("5.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult goal826 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("17.0", PredicateValue.TRUE), new ExpectedPredicateResult("18.0", PredicateValue.TRUE), new ExpectedPredicateResult("20.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult goal630 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("13.0", PredicateValue.FALSE)));
//      ExpectedPredicateEvaluationResult goal792 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("9.0", PredicateValue.TRUE), new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.0", PredicateValue.TRUE), new ExpectedPredicateResult("12.0", PredicateValue.TRUE), new ExpectedPredicateResult("13.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult goal1024 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult goal1161 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE)));
//      // Perform test
//      doPredicateEvaluationTest("examples/_testcase/set/predicateArrayUtil/test/ArrayUtil.proof", 
//                                "examples/_testcase/set/predicateArrayUtil/oracle/ArrayUtil.xml",
//                                true,
//                                true,
//                                goal97,
//                                goal826,
//                                goal630,
//                                goal792,
//                                goal1024,
//                                goal1161);
//   }
   
   /**
    * Tests example: examples/_testcase/set/predicateSimpleInstanceMethodContractApplication
    */
   public void testSimpleInstanceMethodContractApplication_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("12.0", PredicateValue.TRUE), new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("9.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("5.0", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateSimpleInstanceMethodContractApplication/test/SimpleInstanceMethodContractApplication_NoOneStepSimplification.proof", 
                                "examples/_testcase/set/predicateSimpleInstanceMethodContractApplication/oracle/SimpleInstanceMethodContractApplication.xml",
                                true,
                                false,
                                preResult,
                                terminationResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateSimpleInstanceMethodContractApplication
    */
   public void testSimpleInstanceMethodContractApplication() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("12.0", PredicateValue.TRUE), new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("9.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("5.0", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateSimpleInstanceMethodContractApplication/test/SimpleInstanceMethodContractApplication.proof", 
                                "examples/_testcase/set/predicateSimpleInstanceMethodContractApplication/oracle/SimpleInstanceMethodContractApplication.xml",
                                true,
                                false,
                                preResult,
                                terminationResult);
   }

   /**
    * Tests example: examples/_testcase/set/predicateSimpleMethodContractApplication
    */
   public void testSimpleMethodContractApplication_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("9.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("5.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", null)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateSimpleMethodContractApplication/test/SimpleMethodContractApplication_NoOneStepSimplification.proof", 
                                "examples/_testcase/set/predicateSimpleMethodContractApplication/oracle/SimpleMethodContractApplication.xml",
                                true,
                                false,
                                preResult,
                                terminationResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateSimpleMethodContractApplication
    */
   public void testSimpleMethodContractApplication() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("9.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("5.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", null)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateSimpleMethodContractApplication/test/SimpleMethodContractApplication.proof", 
                                "examples/_testcase/set/predicateSimpleMethodContractApplication/oracle/SimpleMethodContractApplication.xml",
                                true,
                                false,
                                preResult,
                                terminationResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateDifferentBranchesTest
    */
   public void testDifferentBranchesTest() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult firstResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult secondResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.FALSE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult thirdResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("1.0", PredicateValue.FALSE)));
      ExpectedPredicateEvaluationResult fourthResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("1.0", PredicateValue.FALSE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateDifferentBranchesTest/test/DifferentBranchesTest.proof", 
                                "examples/_testcase/set/predicateDifferentBranchesTest/oracle/DifferentBranchesTest.xml",
                                false,
                                false,
                                firstResult,
                                secondResult,
                                thirdResult,
                                fourthResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateMultiplePredicateResults
    */
   public void testMultiplePredicateResultsTest() throws Exception {
      // Create expected results
      ExpectedBranchResult goal102 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.FALSE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE));
      ExpectedBranchResult goal95 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE));
      ExpectedPredicateEvaluationResult expectedResult = new ExpectedPredicateEvaluationResult(goal102, goal95);
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateMultiplePredicateResults/test/MultiplePredicateResultsTest.java", 
                                "MultiplePredicateResultsTest[MultiplePredicateResultsTest::main(MultiplePredicateResultsTest,MultiplePredicateResultsTest)].JML normal_behavior operation contract.0", 
                                "examples/_testcase/set/predicateMultiplePredicateResults/oracle/MultiplePredicateResultsTest.xml",
                                false,
                                false,
                                expectedResult);
   }
   
   /**
    * Performs an {@link PredicateEvaluationUtil} test.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param baseContractName The name of the contract.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvariants Use loop invariants?
    * @param expectedResults The expected results.
    * @throws Exception Occurred Exception.
    */
   protected void doPredicateEvaluationTest(String proofFilePathInBaseDir,
                                            String oraclePathInBaseDirFile,
                                            boolean useOperationContracts,
                                            boolean useLoopInvariants,
                                            ExpectedPredicateEvaluationResult... expectedResults) throws Exception {
      SymbolicExecutionEnvironment<CustomUserInterface> env = null;
      try {
         // Perform symbolic execution
         env = doSETTest(keyRepDirectory, 
                         proofFilePathInBaseDir, 
                         oraclePathInBaseDirFile, 
                         false, 
                         false, 
                         false, 
                         false, 
                         false, 
                         useOperationContracts, 
                         useLoopInvariants, 
                         false, 
                         false, 
                         false, 
                         false, 
                         false,
                         true);
         assertNotNull(env);
         // Evaluate predicates
         doPredicateEvaluationTest(env, expectedResults);
      }
      finally {
         if (env != null) {
            env.dispose();
         }
      }
   }
   
   /**
    * Performs an {@link PredicateEvaluationUtil} test.
    * @param javaPathInBaseDir The path to the java file inside the base directory.
    * @param baseContractName The name of the contract.
    * @param oraclePathInBaseDirFile The path to the oracle file inside the base directory.
    * @param useOperationContracts Use operation contracts?
    * @param useLoopInvariants Use loop invariants?
    * @param expectedResults The expected results.
    * @throws Exception Occurred Exception.
    */
   protected void doPredicateEvaluationTest(String javaPathInBaseDir,
                                            String baseContractName,
                                            String oraclePathInBaseDirFile,
                                            boolean useOperationContracts,
                                            boolean useLoopInvariants,
                                            ExpectedPredicateEvaluationResult... expectedResults) throws Exception {
      SymbolicExecutionEnvironment<CustomUserInterface> env = null;
      try {
         // Perform symbolic execution
         env = doSETTest(keyRepDirectory, 
                         javaPathInBaseDir, 
                         baseContractName, 
                         oraclePathInBaseDirFile,
                         false,
                         false,
                         false,
                         false,
                         ALL_IN_ONE_RUN,
                         false,
                         useOperationContracts,
                         useLoopInvariants,
                         false,
                         false,
                         false,
                         false,
                         false,
                         true);
         // Evaluate predicates
         doPredicateEvaluationTest(env, expectedResults);
      }
      finally {
         if (env != null) {
            env.dispose();
         }
      }
   }
   
   /**
    * Performs an {@link PredicateEvaluationUtil} test.
    * @param env The {@link SymbolicExecutionEnvironment} to use.
    * @param expectedResults The expected results.
    * @throws Exception Occurred Exception.
    */
   protected void doPredicateEvaluationTest(SymbolicExecutionEnvironment<CustomUserInterface> env, 
                                            ExpectedPredicateEvaluationResult... expectedResults) throws Exception {
      // Compute current results
      List<PredicateEvaluationResult> currentResults = new LinkedList<PredicateEvaluationResult>();
      ExecutionNodePreorderIterator iter = new ExecutionNodePreorderIterator(env.getBuilder().getStartNode());
      while (iter.hasNext()) {
         IExecutionNode<?> next = iter.next();
         Node nodeToEvaluate;
         if (next instanceof IExecutionTermination) {
            nodeToEvaluate = next.getProofNode();
         }
         else if (next instanceof IExecutionOperationContract) {
            nodeToEvaluate = next.getProofNode().child(2); // Precondition branch
         }
         else if (next instanceof IExecutionLoopInvariant) {
            nodeToEvaluate = next.getProofNode().child(0); // Initial
         }
         else {
            nodeToEvaluate = null;
         }
         if (nodeToEvaluate != null) {
            PredicateEvaluationResult result = PredicateEvaluationUtil.evaluate(nodeToEvaluate, PredicateTermLabel.NAME, false, false);
            currentResults.add(result);
            if (CREATE_NEW_ORACLE_FILES_IN_TEMP_DIRECTORY) {
               System.out.println("\nFound Result:");
               System.out.println(result);
            }
         }
      }
      // Compare results
      assertResults(expectedResults, currentResults);
   }

   /**
    * Asserts the results.
    * @param expected The expected results.
    * @param current The current results.
    */
   protected void assertResults(ExpectedPredicateEvaluationResult[] expected, List<PredicateEvaluationResult> current) {
      assertEquals(expected.length, current.size());
      int i = 0;
      Iterator<PredicateEvaluationResult> currentIter = current.iterator();
      while (i < expected.length && currentIter.hasNext()) {
         assertPredicateRresults(expected[i], currentIter.next());
         i++;
      }
      assertEquals(expected.length, i);
      assertFalse(currentIter.hasNext());
   }
   
   /**
    * Asserts the predicate results.
    * @param expected The expected results.
    * @param current The current results.
    */
   protected void assertPredicateRresults(ExpectedPredicateEvaluationResult expected, PredicateEvaluationResult current) {
      BranchResult[] currentResults = current.getBranchResults();
      assertEquals(expected.branchResults.length, currentResults.length);
      for (int i = 0; i < currentResults.length; i++) {
         assertBranchResult(expected.branchResults[i], currentResults[i]);
      }
   }

   /**
    * Asserts the branch results.
    * @param expected The expected results.
    * @param current The current results.
    */
   protected void assertBranchResult(ExpectedBranchResult expected, BranchResult current) {
      Map<String, IPredicateInstruction> currentResults = current.getResults();
      assertTrue(expected.predicateResults.size() <= currentResults.size());
      for (Entry<String, PredicateValue> expectedEntry : expected.predicateResults.entrySet()) {
         IPredicateInstruction currentInstruction = currentResults.get(expectedEntry.getKey());
         assertNotNull(currentInstruction);
         PredicateResult currentResult = currentInstruction.evaluate(current.getTermLabelName(), currentResults);
         PredicateValue expectedValue = expectedEntry.getValue();
         if (expectedValue == null) {
            assertNull(currentResult);
         }
         else {
            assertNotNull(currentResult);
            assertEquals(expectedValue, currentResult.getValue());
         }
      }
   }

   /**
    * Represents an expected evaluation result.
    * @author Martin Hentschel
    */
   protected static class ExpectedPredicateEvaluationResult {
      /**
       * The expected branches.
       */
      private final ExpectedBranchResult[] branchResults;

      /**
       * Constructor.
       * @param branchResults The expected branches.
       */
      public ExpectedPredicateEvaluationResult(ExpectedBranchResult... branchResults) {
         this.branchResults = branchResults;
      }
   }
   
   /**
    * Represents an expected branch result.
    * @author Martin Hentschel
    */
   protected static class ExpectedBranchResult {
      /**
       * The truth values of all predicates.
       */
      private final Map<String, PredicateValue> predicateResults = new HashMap<String, PredicateValue>();

      /**
       * Constructor.
       * @param predicateResults The truth values of all predicates.
       */
      public ExpectedBranchResult(ExpectedPredicateResult... predicateResults) {
         for (ExpectedPredicateResult result : predicateResults) {
            this.predicateResults.put(result.predicate, result.value);
         }
      }
   }
   
   /**
    * Represents an expected predicate result.
    * @author Martin Hentschel
    */
   protected static class ExpectedPredicateResult {
      /**
       * The predicate.
       */
      private final String predicate;
      
      /**
       * The truth value.
       */
      private final PredicateValue value;
      
      /**
       * Constructor.
       * @param predicate The predicate.
       * @param value The truth value.
       */
      public ExpectedPredicateResult(String predicate, PredicateValue value) {
         this.predicate = predicate;
         this.value = value;
      }
   }
}
