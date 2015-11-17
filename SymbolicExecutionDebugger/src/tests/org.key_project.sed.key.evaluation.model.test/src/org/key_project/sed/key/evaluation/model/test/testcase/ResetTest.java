package org.key_project.sed.key.evaluation.model.test.testcase;

import org.junit.Test;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.TestEvaluation;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;

/**
 * Tests reset of evaluation model elements.
 * @author Martin Hentschel
 */
public class ResetTest extends AbstractEvaluationModelTest {
   /**
    * Tests reset of {@link TestEvaluation#INSTANCE}.
    */
   @Test
   public void testResetOnTestEvaluation() {
      doResetTest(TestEvaluation.INSTANCE);
   }

   /**
    * Tests reset of {@link UnderstandingProofAttemptsEvaluation#INSTANCE}.
    */
   @Test
   public void testResetOnUnderstandingProofAttemptsEvaluation() {
      doResetTest(UnderstandingProofAttemptsEvaluation.INSTANCE);
   }
   
   /**
    * Performs a reset test.
    * @param evaluation The {@link AbstractEvaluation} to test.
    */
   protected void doResetTest(AbstractEvaluation evaluation) {
      // Create initial content
      EvaluationInput input = new EvaluationInput(evaluation);
      fillEvaluationInput(input);
      // Perform reset
      input.reset();
      // Perform test
      assertEvaluationInput(new EvaluationInput(evaluation), input, true, true, ValueComparison.EQUAL);
      // Perform a second reset
      input.reset();
      // Test model again
      assertEvaluationInput(new EvaluationInput(evaluation), input, true, true, ValueComparison.EQUAL);
   }
}
