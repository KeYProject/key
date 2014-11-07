package de.uka.ilkd.key.symbolic_execution;

/**
 * Tests for {@link ExecutionVariableExtractor}.
 * @author Martin Hentschel
 */
public class TestExecutionVariableExtractor extends AbstractSymbolicExecutionTestCase {
   /**
    * Tests example: examples/_testcase/set/variablesConditionalValuesTest
    */
   public void testVariablesConditionalValuesTest_next() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/variablesConditionalValuesTest/test/ConditionalValuesTest.java", 
                "ConditionalValuesTest", 
                "mainNext", 
                null,
                "examples/_testcase/set/variablesConditionalValuesTest/oracle/ConditionalValuesTest_next.xml",
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
                true);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesConditionalValuesTest
    */
   public void testVariablesConditionalValuesTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/variablesConditionalValuesTest/test/ConditionalValuesTest.java", 
                "ConditionalValuesTest", 
                "main", 
                null,
                "examples/_testcase/set/variablesConditionalValuesTest/oracle/ConditionalValuesTest.xml",
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
                true);
   }
   
   /**
    * Tests example: examples/_testcase/set/variableVariablesArrayTest
    */
   public void testVariableVariablesArrayTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/variableVariablesArrayTest/test/VariablesArrayTest.java", 
                "VariablesArrayTest", 
                "arrayTest", 
                null,
                "examples/_testcase/set/variableVariablesArrayTest/oracle/VariablesArrayTest.xml",
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
                true);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesLocalVariablesTest
    */
   public void testVariablesLocalVariablesTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/variablesLocalVariablesTest/test/LocalVariablesTest.java", 
                "LocalVariablesTest", 
                "main", 
                null,
                "examples/_testcase/set/variablesLocalVariablesTest/oracle/LocalVariablesTest.xml",
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
                true);
   }
   
   /**
    * Tests example: examples/_testcase/set/variablesUpdateVariablesTest
    */
   public void testUpdateVariablesTest() throws Exception {
      doSETTest(keyRepDirectory, 
                "examples/_testcase/set/variablesUpdateVariablesTest/test/UpdateVariablesTest.java", 
                "UpdateVariablesTest", 
                "main", 
                null,
                "examples/_testcase/set/variablesUpdateVariablesTest/oracle/UpdateVariablesTest.xml",
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
                true);
   }
}
