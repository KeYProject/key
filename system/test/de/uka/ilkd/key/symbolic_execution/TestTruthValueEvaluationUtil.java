package de.uka.ilkd.key.symbolic_execution;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.logic.label.FormulaTermLabel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.TruthValueEvaluationUtil.BranchResult;
import de.uka.ilkd.key.symbolic_execution.TruthValueEvaluationUtil.MultiEvaluationResult;
import de.uka.ilkd.key.symbolic_execution.TruthValueEvaluationUtil.TruthValueEvaluationResult;
import de.uka.ilkd.key.symbolic_execution.TruthValueEvaluationUtil.TruthValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopInvariant;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Tests for {@link TruthValueEvaluationUtil}.
 * @author Martin Hentschel
 */
public class TestTruthValueEvaluationUtil extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests example: examples/_testcase/set/truthValueEquivExample
    */
   public void testEquivExample_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedBranchResult goal79 = new ExpectedBranchResult(new ExpectedPredicateResult("2.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("4.0", TruthValue.TRUE));
      ExpectedBranchResult goal91 = new ExpectedBranchResult(new ExpectedPredicateResult("1.0", TruthValue.TRUE), new ExpectedPredicateResult("2.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("4.0", TruthValue.TRUE), new ExpectedPredicateResult("5.0", TruthValue.TRUE));
      ExpectedBranchResult goal95 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE));
      ExpectedBranchResult goal97 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("5.0", TruthValue.FALSE)); // SETAccumulate is false
      ExpectedPredicateEvaluationResult result = new ExpectedPredicateEvaluationResult(goal79, goal91, goal95, goal97);
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueEquivExample/test/EquivExampleNoOneStepSimplification.proof", 
                                "examples/_testcase/set/truthValueEquivExample/oracle/EquivExample.xml",
                                false,
                                true,
                                result);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueEquivExample
    */
   public void testEquivExample() throws Exception {
      // Create expected results
      ExpectedBranchResult goal39 = new ExpectedBranchResult(new ExpectedPredicateResult("2.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("4.0", TruthValue.TRUE));
      ExpectedBranchResult goal50 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("5.0", TruthValue.TRUE));
      ExpectedBranchResult goal53 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("5.0", TruthValue.TRUE));
      ExpectedBranchResult goal55 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("5.0", TruthValue.FALSE)); // SETAccumulate is false
      ExpectedPredicateEvaluationResult result = new ExpectedPredicateEvaluationResult(goal39, goal50, goal53, goal55);
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueEquivExample/test/EquivExample.proof", 
                                "examples/_testcase/set/truthValueEquivExample/oracle/EquivExample.xml",
                                false,
                                false,
                                result);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueIfThenElseIntegerTest
    */
   public void testIfThenElseInteger() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult thenResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult elseResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueIfThenElseIntegerTest/test/IfThenElseIntegerTest.java", 
                                "IfThenElseIntegerTest[IfThenElseIntegerTest::magic(int,int)].JML normal_behavior operation contract.0", 
                                "examples/_testcase/set/truthValueIfThenElseIntegerTest/oracle/IfThenElseIntegerTest.xml",
                                false,
                                false,
                                thenResult,
                                elseResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueIfThenElseNotFormulaTest
    */
   public void testIfThenElseNotFormula() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult thenResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult elseResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueIfThenElseNotFormulaTest/test/IfThenElseNotFormulaTest.java", 
                                "IfThenElseNotFormulaTest[IfThenElseNotFormulaTest::magic(int,int)].JML normal_behavior operation contract.0", 
                                "examples/_testcase/set/truthValueIfThenElseNotFormulaTest/oracle/IfThenElseNotFormulaTest.xml",
                                false,
                                false,
                                thenResult,
                                elseResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueIfThenElseFormulaTest
    */
   public void testIfThenElseFormula() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult thenResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("4.0", TruthValue.TRUE), new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult elseResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("4.0", TruthValue.TRUE), new ExpectedPredicateResult("0.0", TruthValue.FALSE), new ExpectedPredicateResult("2.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueIfThenElseFormulaTest/test/IfThenElseFormulaTest.java", 
                                "IfThenElseFormulaTest[IfThenElseFormulaTest::magic(int,int)].JML normal_behavior operation contract.0", 
                                "examples/_testcase/set/truthValueIfThenElseFormulaTest/oracle/IfThenElseFormulaTest.xml",
                                false,
                                false,
                                thenResult,
                                elseResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueNotLastEvaluationGivesTruthValue
    */
   public void testNotLastEvaluationGivesTruthValue() throws Exception {
      // Create expected results
      ExpectedBranchResult goal53 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("6.0", TruthValue.TRUE), new ExpectedPredicateResult("4.0", TruthValue.TRUE), new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("8.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE), new ExpectedPredicateResult("1.12", TruthValue.FALSE), new ExpectedPredicateResult("1.13", TruthValue.TRUE), new ExpectedPredicateResult("2.0", TruthValue.TRUE));
      ExpectedBranchResult goal41 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("0.0", TruthValue.TRUE));
      ExpectedBranchResult goal39 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("0.0", TruthValue.TRUE));
      ExpectedBranchResult goal55 = new ExpectedBranchResult(new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.11", TruthValue.TRUE));
      ExpectedPredicateEvaluationResult result = new ExpectedPredicateEvaluationResult(goal53, goal41, goal39, goal55);
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueNotLastEvaluationGivesTruthValue/test/NotLastEvaluationGivesTruthValue.proof", 
                                "examples/_testcase/set/truthValueNotLastEvaluationGivesTruthValue/oracle/NotLastEvaluationGivesTruthValue.xml",
                                false,
                                true,
                                result);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueArraySumWhile
    */
   public void testArraySumWhile_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult initialResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("14.0", TruthValue.TRUE), new ExpectedPredicateResult("15.0", TruthValue.TRUE), new ExpectedPredicateResult("16.0", TruthValue.TRUE), new ExpectedPredicateResult("17.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult preservesResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("18.0", TruthValue.TRUE), new ExpectedPredicateResult("19.0", TruthValue.TRUE), new ExpectedPredicateResult("20.0", TruthValue.TRUE), new ExpectedPredicateResult("21.0", TruthValue.TRUE), new ExpectedPredicateResult("22.0", TruthValue.TRUE), new ExpectedPredicateResult("23.0", TruthValue.TRUE), new ExpectedPredicateResult("24.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE), new ExpectedPredicateResult("2.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("4.0", TruthValue.FALSE), new ExpectedPredicateResult("8.0", TruthValue.TRUE), new ExpectedPredicateResult("9.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueArraySumWhile/test/ArraySumWhileNoOneStepSimplification.proof", 
                                "examples/_testcase/set/truthValueArraySumWhile/oracle/ArraySumWhile.xml",
                                false,
                                true,
                                initialResult,
                                preservesResult,
                                terminationResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueArraySumWhile
    */
   public void testArraySumWhile() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult initialResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("14.0", TruthValue.TRUE), new ExpectedPredicateResult("15.0", TruthValue.TRUE), new ExpectedPredicateResult("16.0", TruthValue.TRUE), new ExpectedPredicateResult("17.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult preservesResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("18.0", TruthValue.TRUE), new ExpectedPredicateResult("19.0", TruthValue.TRUE), new ExpectedPredicateResult("20.0", TruthValue.TRUE), new ExpectedPredicateResult("21.0", TruthValue.TRUE), new ExpectedPredicateResult("22.0", TruthValue.TRUE), new ExpectedPredicateResult("23.0", TruthValue.TRUE), new ExpectedPredicateResult("24.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE), new ExpectedPredicateResult("2.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE), new ExpectedPredicateResult("4.0", TruthValue.FALSE), new ExpectedPredicateResult("8.0", TruthValue.TRUE), new ExpectedPredicateResult("9.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueArraySumWhile/test/ArraySumWhile.proof", 
                                "examples/_testcase/set/truthValueArraySumWhile/oracle/ArraySumWhile.xml",
                                false,
                                true,
                                initialResult,
                                preservesResult,
                                terminationResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueArrayUtil
    */
   public void testArrayUtil_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult goal97 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("5.0", TruthValue.TRUE), new ExpectedPredicateResult("6.0", TruthValue.TRUE), new ExpectedPredicateResult("7.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult goal826 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("17.0", TruthValue.TRUE), new ExpectedPredicateResult("18.0", TruthValue.TRUE), new ExpectedPredicateResult("20.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult goal630 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("8.0", TruthValue.TRUE), new ExpectedPredicateResult("10.0", TruthValue.TRUE), new ExpectedPredicateResult("13.0", TruthValue.FALSE)));
      ExpectedPredicateEvaluationResult goal792 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("8.0", TruthValue.TRUE), new ExpectedPredicateResult("9.0", TruthValue.TRUE), new ExpectedPredicateResult("10.0", TruthValue.TRUE), new ExpectedPredicateResult("11.0", TruthValue.TRUE), new ExpectedPredicateResult("12.0", TruthValue.TRUE), new ExpectedPredicateResult("13.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult goal1024 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult goal1161 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueArrayUtil/test/ArrayUtilNoOneStepSimplification.proof", 
                                "examples/_testcase/set/truthValueArrayUtil/oracle/ArrayUtil.xml",
                                true,
                                true,
                                goal97,
                                goal826,
                                goal630,
                                goal792,
                                goal1024,
                                goal1161);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueArrayUtil
    */
   public void testArrayUtil() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult goal97 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("5.0", TruthValue.TRUE), new ExpectedPredicateResult("6.0", TruthValue.TRUE), new ExpectedPredicateResult("7.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult goal826 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("17.0", TruthValue.TRUE), new ExpectedPredicateResult("18.0", TruthValue.TRUE), new ExpectedPredicateResult("20.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult goal630 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("8.0", TruthValue.TRUE), new ExpectedPredicateResult("10.0", TruthValue.TRUE), new ExpectedPredicateResult("13.0", TruthValue.FALSE)));
      ExpectedPredicateEvaluationResult goal792 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("8.0", TruthValue.TRUE), new ExpectedPredicateResult("9.0", TruthValue.TRUE), new ExpectedPredicateResult("10.0", TruthValue.TRUE), new ExpectedPredicateResult("11.0", TruthValue.TRUE), new ExpectedPredicateResult("12.0", TruthValue.TRUE), new ExpectedPredicateResult("13.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult goal1024 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult goal1161 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("3.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueArrayUtil/test/ArrayUtil.proof", 
                                "examples/_testcase/set/truthValueArrayUtil/oracle/ArrayUtil.xml",
                                true,
                                true,
                                goal97,
                                goal826,
                                goal630,
                                goal792,
                                goal1024,
                                goal1161);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueSimpleInstanceMethodContractApplication
    */
   public void testSimpleInstanceMethodContractApplication_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("12.0", TruthValue.TRUE), new ExpectedPredicateResult("10.0", TruthValue.TRUE), new ExpectedPredicateResult("9.0", TruthValue.TRUE), new ExpectedPredicateResult("11.0", TruthValue.TRUE), new ExpectedPredicateResult("7.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE), new ExpectedPredicateResult("5.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueSimpleInstanceMethodContractApplication/test/SimpleInstanceMethodContractApplication_NoOneStepSimplification.proof", 
                                "examples/_testcase/set/truthValueSimpleInstanceMethodContractApplication/oracle/SimpleInstanceMethodContractApplication.xml",
                                true,
                                false,
                                preResult,
                                terminationResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueSimpleInstanceMethodContractApplication
    */
   public void testSimpleInstanceMethodContractApplication() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("12.0", TruthValue.TRUE), new ExpectedPredicateResult("10.0", TruthValue.TRUE), new ExpectedPredicateResult("9.0", TruthValue.TRUE), new ExpectedPredicateResult("11.0", TruthValue.TRUE), new ExpectedPredicateResult("7.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE), new ExpectedPredicateResult("5.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueSimpleInstanceMethodContractApplication/test/SimpleInstanceMethodContractApplication.proof", 
                                "examples/_testcase/set/truthValueSimpleInstanceMethodContractApplication/oracle/SimpleInstanceMethodContractApplication.xml",
                                true,
                                false,
                                preResult,
                                terminationResult);
   }

   /**
    * Tests example: examples/_testcase/set/truthValueSimpleMethodContractApplication
    */
   public void testSimpleMethodContractApplication_NoOneStepSimplification() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("10.0", TruthValue.TRUE), new ExpectedPredicateResult("9.0", TruthValue.TRUE), new ExpectedPredicateResult("11.0", TruthValue.TRUE), new ExpectedPredicateResult("7.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE), new ExpectedPredicateResult("5.0", TruthValue.TRUE), new ExpectedPredicateResult("2.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueSimpleMethodContractApplication/test/SimpleMethodContractApplication_NoOneStepSimplification.proof", 
                                "examples/_testcase/set/truthValueSimpleMethodContractApplication/oracle/SimpleMethodContractApplication.xml",
                                true,
                                false,
                                preResult,
                                terminationResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueSimpleMethodContractApplication
    */
   public void testSimpleMethodContractApplication() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("10.0", TruthValue.TRUE), new ExpectedPredicateResult("9.0", TruthValue.TRUE), new ExpectedPredicateResult("11.0", TruthValue.TRUE), new ExpectedPredicateResult("7.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE), new ExpectedPredicateResult("5.0", TruthValue.TRUE), new ExpectedPredicateResult("2.0", TruthValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueSimpleMethodContractApplication/test/SimpleMethodContractApplication.proof", 
                                "examples/_testcase/set/truthValueSimpleMethodContractApplication/oracle/SimpleMethodContractApplication.xml",
                                true,
                                false,
                                preResult,
                                terminationResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueDifferentBranchesTest
    */
   public void testDifferentBranchesTest() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult firstResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult secondResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.FALSE), new ExpectedPredicateResult("1.0", TruthValue.TRUE)));
      ExpectedPredicateEvaluationResult thirdResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("1.0", TruthValue.FALSE)));
      ExpectedPredicateEvaluationResult fourthResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("1.0", TruthValue.FALSE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueDifferentBranchesTest/test/DifferentBranchesTest.proof", 
                                "examples/_testcase/set/truthValueDifferentBranchesTest/oracle/DifferentBranchesTest.xml",
                                false,
                                false,
                                firstResult,
                                secondResult,
                                thirdResult,
                                fourthResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/truthValueMultiplePredicateResults
    */
   public void testMultiplePredicateResultsTest() throws Exception {
      // Create expected results
      ExpectedBranchResult goal102 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.FALSE), new ExpectedPredicateResult("1.0", TruthValue.TRUE));
      ExpectedBranchResult goal95 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", TruthValue.TRUE), new ExpectedPredicateResult("1.0", TruthValue.TRUE));
      ExpectedPredicateEvaluationResult expectedResult = new ExpectedPredicateEvaluationResult(goal102, goal95);
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/truthValueMultiplePredicateResults/test/MultiplePredicateResultsTest.java", 
                                "MultiplePredicateResultsTest[MultiplePredicateResultsTest::main(MultiplePredicateResultsTest,MultiplePredicateResultsTest)].JML normal_behavior operation contract.0", 
                                "examples/_testcase/set/truthValueMultiplePredicateResults/oracle/MultiplePredicateResultsTest.xml",
                                false,
                                false,
                                expectedResult);
   }
   
   /**
    * Performs an {@link TruthValueEvaluationUtil} test.
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
    * Performs an {@link TruthValueEvaluationUtil} test.
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
    * Performs an {@link TruthValueEvaluationUtil} test.
    * @param env The {@link SymbolicExecutionEnvironment} to use.
    * @param expectedResults The expected results.
    * @throws Exception Occurred Exception.
    */
   protected void doPredicateEvaluationTest(SymbolicExecutionEnvironment<CustomUserInterface> env, 
                                            ExpectedPredicateEvaluationResult... expectedResults) throws Exception {
      // Compute current results
      List<TruthValueEvaluationResult> currentResults = new LinkedList<TruthValueEvaluationResult>();
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
            TruthValueEvaluationResult result = TruthValueEvaluationUtil.evaluate(nodeToEvaluate, FormulaTermLabel.NAME, false, false);
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
   protected void assertResults(ExpectedPredicateEvaluationResult[] expected, List<TruthValueEvaluationResult> current) {
      assertEquals(expected.length, current.size());
      int i = 0;
      Iterator<TruthValueEvaluationResult> currentIter = current.iterator();
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
   protected void assertPredicateRresults(ExpectedPredicateEvaluationResult expected, TruthValueEvaluationResult current) {
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
      Map<String, MultiEvaluationResult> currentResults = current.getResults();
      assertTrue(expected.predicateResults.size() <= currentResults.size());
      for (Entry<String, TruthValue> expectedEntry : expected.predicateResults.entrySet()) {
         MultiEvaluationResult currentInstruction = currentResults.get(expectedEntry.getKey());
         assertNotNull(currentInstruction);
         TruthValue currentResult = currentInstruction.evaluate(current.getTermLabelName(), currentResults);
         TruthValue expectedValue = expectedEntry.getValue();
         if (expectedValue == null) {
            assertNull(currentResult);
         }
         else {
            assertNotNull(currentResult);
            assertEquals(expectedValue, currentResult);
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
      private final Map<String, TruthValue> predicateResults = new HashMap<String, TruthValue>();

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
      private final TruthValue value;
      
      /**
       * Constructor.
       * @param predicate The predicate.
       * @param value The truth value.
       */
      public ExpectedPredicateResult(String predicate, TruthValue value) {
         this.predicate = predicate;
         this.value = value;
      }
   }
}
