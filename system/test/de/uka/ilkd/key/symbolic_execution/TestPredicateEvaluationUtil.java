package de.uka.ilkd.key.symbolic_execution;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uka.ilkd.key.logic.label.PredicateTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.PredicateEvaluationUtil.BranchResult;
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
    * Tests example: examples/_testcase/set/predicateArraySumWhile
    */
   public void testArraySumWhile() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult initialResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(9)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(10)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(7)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(8)", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult preservesResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(14)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(17)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(11)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(13)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(16)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(12)", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(0)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(1)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(2)", PredicateValue.TRUE)));
      // Perform test
      doPredicateEvaluationTest("examples/_testcase/set/predicateArraySumWhile/test/ArraySumWhile.java", 
                                "ArraySumWhile[ArraySumWhile::sum([I)].JML operation contract.0", 
                                "examples/_testcase/set/predicateArraySumWhile/oracle/ArraySumWhile.xml",
                                false,
                                true,
                                initialResult,
                                preservesResult,
                                terminationResult);
   }
   
   /**
    * Tests example: examples/_testcase/set/predicateSimpleInstanceMethodContractApplication
    */
   public void testSimpleInstanceMethodContractApplication() throws Exception {
      // Create expected results
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(6)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(8)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(7)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(4)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(9)", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(1)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(0)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(3)", PredicateValue.TRUE)));
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
      ExpectedPredicateEvaluationResult preResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(8)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(4)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(6)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(7)", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult terminationResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(1)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(0)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(3)", PredicateValue.TRUE)));
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
      ExpectedPredicateEvaluationResult firstResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(0)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(1)", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult secondResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(0)", PredicateValue.FALSE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(1)", PredicateValue.TRUE)));
      ExpectedPredicateEvaluationResult thirdResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(1)", PredicateValue.FALSE)));
      ExpectedPredicateEvaluationResult fourthResult = new ExpectedPredicateEvaluationResult(new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(1)", PredicateValue.FALSE)));
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
      ExpectedBranchResult goal102 = new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(0)", PredicateValue.FALSE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(1)", PredicateValue.TRUE));
      ExpectedBranchResult goal95 = new ExpectedBranchResult(new ExpectedPredicateResult(PredicateTermLabel.NAME + "(0)", PredicateValue.TRUE), new ExpectedPredicateResult(PredicateTermLabel.NAME + "(1)", PredicateValue.TRUE));
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
      finally {
         if (env != null) {
            env.dispose();
         }
      }
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
      Map<TermLabel, PredicateResult> currentResults = current.getResults();
      assertEquals(expected.predicateResults.size(), currentResults.size());
      for (Entry<TermLabel, PredicateResult> currentEntry : currentResults.entrySet()) {
         PredicateValue expectedValue = expected.predicateResults.get(currentEntry.getKey().toString());
         assertNotNull(expectedValue);
         assertNotNull(currentEntry.getValue());
         assertEquals(expectedValue, currentEntry.getValue().getValue());
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
