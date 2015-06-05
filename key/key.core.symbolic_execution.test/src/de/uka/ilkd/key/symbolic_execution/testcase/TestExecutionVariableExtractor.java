package de.uka.ilkd.key.symbolic_execution.testcase;

import de.uka.ilkd.key.symbolic_execution.ExecutionVariableExtractor;

/**
 * Tests for {@link ExecutionVariableExtractor}.
 * @author Martin Hentschel
 */
public class TestExecutionVariableExtractor extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests example: /set/variableVariableMethodContractTest
    */
   public void testVariableMethodContractTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variableVariableMethodContractTest/test/VariableMethodContractTest.java", 
                "VariableMethodContractTest", 
                "findMax", 
                null,
                "/set/variableVariableMethodContractTest/oracle/VariableMethodContractTest.xml",
                false,
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
                true,
                true);
   }
   
   /**
    * Tests example: /set/variablesConditionalCycle
    */
   public void testVariablesConditionalCycle() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variablesConditionalCycle/test/VariablesConditionalCycle.java", 
                "VariablesConditionalCycle", 
                "main", 
                null,
                "/set/variablesConditionalCycle/oracle/VariablesConditionalCycle.xml",
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
                true,
                true);
   }
   
   /**
    * Tests example: /set/variablesSimpleCycle
    */
   public void testVariablesSimpleCycle() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variablesSimpleCycle/test/VariablesSimpleCycle.java", 
                "VariablesSimpleCycle", 
                "main", 
                "something != null",
                "/set/variablesSimpleCycle/oracle/VariablesSimpleCycle.xml",
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
                true,
                true);
   }
   
   /**
    * Tests example: /set/variablesWithQuantifier
    */
   public void testVariablesWithQuantifier() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variablesWithQuantifier/test/EnoughInfoReturn.java", 
                "EnoughInfoReturn", 
                "passwordChecker", 
                "passwords != null",
                "/set/variablesWithQuantifier/oracle/EnoughInfoReturn.xml",
                false,
                true,
                false,
                false,
                DEFAULT_MAXIMAL_SET_NODES_PER_RUN,
                false,
                false,
                true,
                false,
                false,
                false,
                false,
                true,
                true);
   }
   
   /**
    * Tests example: /set/variablesVariableArrayIndex
    */
   public void testVariableArrayIndex() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variablesVariableArrayIndex/test/VariableArrayIndex.java", 
                "VariableArrayIndex", 
                "magic", 
                "array != null && array.length >= 1 && index >= 0 && index < array.length",
                "/set/variablesVariableArrayIndex/oracle/VariableArrayIndex.xml",
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
                true,
                true);
   }

   /**
    * Tests example: /set/variablesConditionalValuesTest
    */
   public void testVariablesConditionalValuesTest_next() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variablesConditionalValuesTest/test/ConditionalValuesTest.java", 
                "ConditionalValuesTest", 
                "mainNext", 
                null,
                "/set/variablesConditionalValuesTest/oracle/ConditionalValuesTest_next.xml",
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
                true,
                true);
   }
   
   /**
    * Tests example: /set/variablesConditionalValuesTest
    */
   public void testVariablesConditionalValuesTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variablesConditionalValuesTest/test/ConditionalValuesTest.java", 
                "ConditionalValuesTest", 
                "main", 
                null,
                "/set/variablesConditionalValuesTest/oracle/ConditionalValuesTest.xml",
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
                true,
                true);
   }
   
   /**
    * Tests example: /set/variableVariablesArrayTest
    */
   public void testVariableVariablesArrayTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variableVariablesArrayTest/test/VariablesArrayTest.java", 
                "VariablesArrayTest", 
                "arrayTest", 
                null,
                "/set/variableVariablesArrayTest/oracle/VariablesArrayTest.xml",
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
                true,
                true);
   }
   
   /**
    * Tests example: /set/variablesLocalVariablesTest
    */
   public void testVariablesLocalVariablesTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variablesLocalVariablesTest/test/LocalVariablesTest.java", 
                "LocalVariablesTest", 
                "main", 
                null,
                "/set/variablesLocalVariablesTest/oracle/LocalVariablesTest.xml",
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
                true,
                true);
   }
   
   /**
    * Tests example: /set/variablesUpdateVariablesTest
    */
   public void testUpdateVariablesTest() throws Exception {
      doSETTest(testCaseDirectory, 
                "/set/variablesUpdateVariablesTest/test/UpdateVariablesTest.java", 
                "UpdateVariablesTest", 
                "main", 
                null,
                "/set/variablesUpdateVariablesTest/oracle/UpdateVariablesTest.xml",
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
                true,
                true);
   }
}
