package de.uka.ilkd.key.symbolic_execution;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.ui.CustomUserInterface;

/**
 * Tests the conditional values provided by {@link IExecutionNode#getVariables(de.uka.ilkd.key.logic.Term)}.
 * @author Martin Hentschel
 */
public class TestConditionalVariables extends AbstractSymbolicExecutionTestCase {
   /**
    * Compares the conditional values on the {@code Number} example.
    * @throws Exception Occurred Exception.
    */
   public void testVariablesUnderMethodReturnCondition() throws Exception {
      SymbolicExecutionEnvironment<CustomUserInterface> env = doSETTest(keyRepDirectory, 
                                                                        "examples/_testcase/set/conditionalVariables/test/Number.java", 
                                                                        "Number", 
                                                                        "equals", 
                                                                        null, 
                                                                        "examples/_testcase/set/conditionalVariables/oracle/Number.xml", 
                                                                        false, 
                                                                        false, 
                                                                        false, 
                                                                        false, 
                                                                        1000, 
                                                                        false, 
                                                                        false, 
                                                                        false, 
                                                                        false, 
                                                                        false, 
                                                                        false, 
                                                                        false,
                                                                        false);
      try {
         // Find nodes in tree
         IExecutionStart start = env.getBuilder().getStartNode();
         IExecutionNode<?> call = start.getChildren()[0];
         IExecutionNode<?> ifStatement = call.getChildren()[0];
         IExecutionNode<?> notNullCondition = ifStatement.getChildren()[0];
         IExecutionNode<?> equalCondition = notNullCondition.getChildren()[0];
         IExecutionNode<?> returnTrueStatement = equalCondition.getChildren()[0];
         IExecutionBaseMethodReturn<?> returnTrue = (IExecutionBaseMethodReturn<?>)returnTrueStatement.getChildren()[0];
         IExecutionNode<?> notEqualCondition = notNullCondition.getChildren()[1];
         IExecutionNode<?> returnFalseStatement = notEqualCondition.getChildren()[0];
         IExecutionBaseMethodReturn<?> returnFalse = (IExecutionBaseMethodReturn<?>)returnFalseStatement.getChildren()[0];
         IExecutionNode<?> nullCondition = ifStatement.getChildren()[1];
         IExecutionBaseMethodReturn<?> exceptionalReturn = (IExecutionBaseMethodReturn<?>)nullCondition.getChildren()[0];
         // Test conditional values on if statement (call node provides only exc) under method return condition
         assertConditionalVariables(createExpectedEqualCaseVariables(), ifStatement, returnTrue.getMethodReturnCondition(), true, true, false);
         assertConditionalVariables(createExpectedNotEqualCaseVariables(), ifStatement, returnFalse.getMethodReturnCondition(), true, true, false);
         assertConditionalVariables(createExpectedNullCaseVariables(), ifStatement, exceptionalReturn.getMethodReturnCondition(), true, true, false);
      }
      finally {
         env.dispose();
      }
   }
   
   /**
    * Ensures that the result of {@link IExecutionNode#getVariables(Term)} is correct.
    * @param expected The expected {@link IExecutionVariable}s.
    * @param node The current {@link IExecutionNode} to call {@link IExecutionNode#getVariables(Term)} on.
    * @param condition The condition to use.
    * @param compareParent Compare parents?
    * @param compareChildren Compare children?
    * @param compareConstraints Compare constraints?
    * @throws ProofInputException Occurred Exception.
    */
   protected static void assertConditionalVariables(IExecutionVariable[] expected, 
                                                    IExecutionNode<?> node,
                                                    Term condition,
                                                    boolean compareParent, 
                                                    boolean compareChildren,
                                                    boolean compareConstraints) throws ProofInputException {
      IExecutionVariable[] current = node.getVariables(condition);
      assertVariables(expected, current, true, true, false);
      IExecutionVariable[] currentAgain = node.getVariables(condition);
      assertSame(current, currentAgain);
      assertVariables(expected, currentAgain, true, true, false);
   }

   /**
    * Creates the expected variables in case that {@code n.content == self.content}.
    * @return The expected {@link IExecutionVariable}s.
    */
   protected IExecutionVariable[] createExpectedEqualCaseVariables() {
      ExecutionNodeReader.KeYlessVariable[] result = new ExecutionNodeReader.KeYlessVariable[3];
      // self
      result[0] = new ExecutionNodeReader.KeYlessVariable(null, false, null, "self");
      ExecutionNodeReader.KeYlessValue selfValue = new ExecutionNodeReader.KeYlessValue(result[0], "Number", "self", "self {true}", false, true, "true");
      result[0].addValue(selfValue);
      ExecutionNodeReader.KeYlessVariable selfContentVar = new ExecutionNodeReader.KeYlessVariable(selfValue, false, null, "content");
      selfContentVar.addValue(new ExecutionNodeReader.KeYlessValue(selfContentVar, "int", "int::select(heap,n,Number::$content)", "content {true}", false, false, "true"));
      selfValue.addChildVariable(selfContentVar);
      // n
      result[1] = new ExecutionNodeReader.KeYlessVariable(null, false, null, "n");
      ExecutionNodeReader.KeYlessValue nValue = new ExecutionNodeReader.KeYlessValue(result[1], "Number", "n", "n {true}", false, true, "true");
      result[1].addValue(nValue);
      ExecutionNodeReader.KeYlessVariable nContentVar = new ExecutionNodeReader.KeYlessVariable(nValue, false, null, "content");
      nContentVar.addValue(new ExecutionNodeReader.KeYlessValue(nContentVar, "int", "int::select(heap,n,Number::$content)", "content {true}", false, false, "true"));
      nValue.addChildVariable(nContentVar);
      // exc
      result[2] = new ExecutionNodeReader.KeYlessVariable(null, false, null, "exc");
      result[2].addValue(new ExecutionNodeReader.KeYlessValue(result[2], "Null", "null", "exc {true}", false, false, "true"));
      return result;
   }

   /**
    * Creates the expected variables in case that {@code n.content != self.content}.
    * @return The expected {@link IExecutionVariable}s.
    */
   protected IExecutionVariable[] createExpectedNotEqualCaseVariables() {
      ExecutionNodeReader.KeYlessVariable[] result = new ExecutionNodeReader.KeYlessVariable[3];
      // self
      result[0] = new ExecutionNodeReader.KeYlessVariable(null, false, null, "self");
      ExecutionNodeReader.KeYlessValue selfValue = new ExecutionNodeReader.KeYlessValue(result[0], "Number", "self", "self {true}", false, true, "true");
      result[0].addValue(selfValue);
      ExecutionNodeReader.KeYlessVariable selfContentVar = new ExecutionNodeReader.KeYlessVariable(selfValue, false, null, "content");
      selfContentVar.addValue(new ExecutionNodeReader.KeYlessValue(selfContentVar, "int", "int::select(heap,self,Number::$content)", "content {true}", false, false, "true"));
      selfValue.addChildVariable(selfContentVar);
      // n
      result[1] = new ExecutionNodeReader.KeYlessVariable(null, false, null, "n");
      ExecutionNodeReader.KeYlessValue nValue = new ExecutionNodeReader.KeYlessValue(result[1], "Number", "n", "n {true}", false, true, "true");
      result[1].addValue(nValue);
      ExecutionNodeReader.KeYlessVariable nContentVar = new ExecutionNodeReader.KeYlessVariable(nValue, false, null, "content");
      nContentVar.addValue(new ExecutionNodeReader.KeYlessValue(nContentVar, "int", "int::select(heap,n,Number::$content)", "content {true}", false, false, "true"));
      nValue.addChildVariable(nContentVar);
      // exc
      result[2] = new ExecutionNodeReader.KeYlessVariable(null, false, null, "exc");
      result[2].addValue(new ExecutionNodeReader.KeYlessValue(result[2], "Null", "null", "exc {true}", false, false, "true"));
      return result;
   }

   /**
    * Creates the expected variables in case that {@code n} is {@code null}.
    * @return The expected {@link IExecutionVariable}s.
    */
   protected IExecutionVariable[] createExpectedNullCaseVariables() {
      ExecutionNodeReader.KeYlessVariable[] result = new ExecutionNodeReader.KeYlessVariable[3];
      // self
      result[0] = new ExecutionNodeReader.KeYlessVariable(null, false, null, "self");
      ExecutionNodeReader.KeYlessValue selfValue = new ExecutionNodeReader.KeYlessValue(result[0], "Number", "self", "self {true}", false, true, "true");
      result[0].addValue(selfValue);
      ExecutionNodeReader.KeYlessVariable selfContentVar = new ExecutionNodeReader.KeYlessVariable(selfValue, false, null, "content");
      selfContentVar.addValue(new ExecutionNodeReader.KeYlessValue(selfContentVar, "int", "int::select(heap,self,Number::$content)", "content {true}", false, false, "true"));
      selfValue.addChildVariable(selfContentVar);
      // n
      result[1] = new ExecutionNodeReader.KeYlessVariable(null, false, null, "n");
      ExecutionNodeReader.KeYlessValue nValue = new ExecutionNodeReader.KeYlessValue(result[1], "Null", "null", "n {true}", false, false, "true");
      result[1].addValue(nValue);
      // exc
      result[2] = new ExecutionNodeReader.KeYlessVariable(null, false, null, "exc");
      result[2].addValue(new ExecutionNodeReader.KeYlessValue(result[2], "Null", "null", "exc {true}", false, false, "true"));
      return result;
   }
}
