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
    * Tests example: examples/_testcase/set/predicateNotLastEvaluationGivesTruthValue
    */
   public void testNotLastEvaluationGivesTruthValue() throws Exception {
      // Create expected results
      ExpectedBranchResult goal53 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.10", PredicateValue.FALSE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.11", PredicateValue.TRUE), new ExpectedPredicateResult("2.0", PredicateValue.TRUE));
      ExpectedBranchResult goal41 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.UNKNOWN), new ExpectedPredicateResult("2.0", PredicateValue.TRUE));
      ExpectedBranchResult goal39 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.UNKNOWN), new ExpectedPredicateResult("2.0", PredicateValue.TRUE));
      ExpectedBranchResult goal55 = new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.9", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("2.0", PredicateValue.TRUE));
      ExpectedPredicateEvaluationResult result = new ExpectedPredicateEvaluationResult(goal53, goal41, goal39, goal55);
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateNotLastEvaluationGivesTruthValue/test/NotLastEvaluationGivesTruthValue.proof", 
                                "examples/_testcase/set/predicateNotLastEvaluationGivesTruthValue/oracle/NotLastEvaluationGivesTruthValue.xml",
                                false,
                                true,
                                result);
   }
   
   // TODO: Make this test working by supporting predicates in rule 'arrayLengthNotNegative'
//   /**
//    * Tests example: examples/_testcase/set/predicateArraySumWhile
//    */
//   public void testArraySumWhile() throws Exception {
//      // Create expected results
//      ExpectedPredicateEvaluationResult initialResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("9.0", PredicateValue.TRUE), new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE), new ExpectedPredicateResult("8.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult preservesResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("14.0", PredicateValue.TRUE), new ExpectedPredicateResult("17.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.0", PredicateValue.TRUE), new ExpectedPredicateResult("13.0", PredicateValue.TRUE), new ExpectedPredicateResult("16.0", PredicateValue.TRUE), new ExpectedPredicateResult("12.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("2.0", PredicateValue.TRUE)));
//      // Perform test
//      doPredicateEvaluationTest("examples/_testcase/set/predicateArraySumWhile/test/ArraySumWhile.java", 
//                                "ArraySumWhile[ArraySumWhile::sum([I)].JML operation contract.0", 
//                                "examples/_testcase/set/predicateArraySumWhile/oracle/ArraySumWhile.xml",
//                                false,
//                                true,
//                                initialResult,
//                                preservesResult,
//                                terminationResult);
//   }
   
// TODO: Make test working by not labeling predicates within quantifiers.
//   /**
//    * Tests example: examples/_testcase/set/predicateArrayUtil
//    */
//   public void testArrayUtil() throws Exception {
//      // Create expected results
//      ExpectedPredicateEvaluationResult goal321 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.1", PredicateValue.FALSE), new ExpectedPredicateResult("4.4", PredicateValue.FALSE), new ExpectedPredicateResult("5.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.2", PredicateValue.FALSE)));
//      ExpectedPredicateEvaluationResult goal396 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("18.0", PredicateValue.TRUE), new ExpectedPredicateResult("16.0", PredicateValue.TRUE), new ExpectedPredicateResult("15.0", PredicateValue.TRUE), new ExpectedPredicateResult("17.0", PredicateValue.FALSE)));
//      ExpectedPredicateEvaluationResult goal503 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("6.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.6", PredicateValue.FALSE), new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.5", PredicateValue.FALSE), new ExpectedPredicateResult("11.0", PredicateValue.FALSE)));
//      ExpectedPredicateEvaluationResult goal480 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("6.3", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.1", PredicateValue.TRUE), new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("10.0", PredicateValue.TRUE), new ExpectedPredicateResult("11.3", PredicateValue.TRUE), new ExpectedPredicateResult("11.2", PredicateValue.TRUE), new ExpectedPredicateResult("11.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult goal418 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("2.0", PredicateValue.TRUE)));
//      ExpectedPredicateEvaluationResult goal416 = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("2.0", PredicateValue.TRUE)));
//      // Perform test
//      doPredicateEvaluationTest("examples/_testcase/set/predicateArrayUtil/test/ArrayUtil.java", 
//                                "ArrayUtil[ArrayUtil::indexOf([Ljava.lang.Object,ArrayUtil.Filter)].JML normal_behavior operation contract.0", 
//                                "examples/_testcase/set/predicateArrayUtil/oracle/ArrayUtil.xml",
//                                true,
//                                true,
//                                goal321,
//                                goal396,
//                                goal503,
//                                goal480,
//                                goal418,
//                                goal416);
//   }
   
   /**
    * Tests example: examples/_testcase/set/predicateSimpleInstanceMethodContractApplication
    */
   public void testSimpleInstanceMethodContractApplication() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("6.0", PredicateValue.TRUE), new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.TRUE), new ExpectedPredicateResult("9.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("0.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateSimpleInstanceMethodContractApplication/test/SimpleInstanceMethodContractApplication.java", 
                                "SimpleInstanceMethodContractApplication[SimpleInstanceMethodContractApplication::main(SimpleInstanceMethodContractApplication)].JML normal_behavior operation contract.0", 
                                "examples/_testcase/set/predicateSimpleInstanceMethodContractApplication/oracle/SimpleInstanceMethodContractApplication.xml",
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
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("8.0", PredicateValue.TRUE), new ExpectedPredicateResult("4.0", PredicateValue.TRUE), new ExpectedPredicateResult("6.0", PredicateValue.TRUE), new ExpectedPredicateResult("7.0", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult("1.0", PredicateValue.TRUE), new ExpectedPredicateResult("3.0", PredicateValue.TRUE), new ExpectedPredicateResult("0.0", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateSimpleMethodContractApplication/test/SimpleMethodContractApplication.java", 
                                "SimpleMethodContractApplication[SimpleMethodContractApplication::main()].JML normal_behavior operation contract.0", 
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
      doPredicateEvaluationTest("examples/_testcase/set/predicateDifferentBranchesTest/test/DifferentBranchesTest.java", 
                                "DifferentBranchesTest[DifferentBranchesTest::main([I)].JML normal_behavior operation contract.0", 
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
                         false);
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
                         false);
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
      assertEquals(expected.predicateResults.size(), currentResults.size());
      for (Entry<String, IPredicateInstruction> currentEntry : currentResults.entrySet()) {
         PredicateValue expectedValue = expected.predicateResults.get(currentEntry.getKey().toString());
         assertNotNull(expectedValue);
         assertNotNull(currentEntry.getValue());
         PredicateResult currentResult = currentEntry.getValue().evaluate(current.getTermLabelName(), currentResults);
         assertNotNull(currentResult);
         assertEquals(expectedValue, currentResult.getValue());
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
