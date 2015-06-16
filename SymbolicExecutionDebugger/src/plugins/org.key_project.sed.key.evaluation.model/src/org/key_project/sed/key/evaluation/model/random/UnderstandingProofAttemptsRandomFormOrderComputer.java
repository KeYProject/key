package org.key_project.sed.key.evaluation.model.random;

import java.util.List;

import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.util.java.CollectionUtil;

public class UnderstandingProofAttemptsRandomFormOrderComputer implements IRandomCompletion {
   @SuppressWarnings("unchecked")
   @Override
   // TODO: Compute a real random order!
   public List<RandomFormInput> computeRandomValues(EvaluationInput evaluationInput, AbstractFormInput<?> currentForm) {
      // Get needed objects
      RandomForm evaluationForm = ((UnderstandingProofAttemptsEvaluation) evaluationInput.getEvaluation()).getEvaluationForm();
      RandomFormInput evaluationFormInput = (RandomFormInput) evaluationInput.getFormInput(evaluationForm);
      AbstractPageInput<?> evaluationPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.EVALUATION_PAGE_NAME);
      AbstractPageInput<?> jmlPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.JML_PAGE_NAME);
      AbstractPageInput<?> keyPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME);
      AbstractPageInput<?> sedPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME);
      AbstractPageInput<?> proof1Page = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.PROOF_1_PAGE_NAME);
      AbstractPageInput<?> proof2Page = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.PROOF_2_PAGE_NAME);
      AbstractPageInput<?> proof3Page = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.PROOF_3_PAGE_NAME);
      AbstractPageInput<?> proof4Page = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.PROOF_4_PAGE_NAME);
      AbstractPageInput<?> feedbackPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.FEEDBACK_PAGE);
      AbstractPageInput<?> sendPage = evaluationFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.SEND_EVALUATION_PAGE_NAME);
      // Set order and tools
      evaluationFormInput.setPageOrder(CollectionUtil.toList(evaluationPage, jmlPage, keyPage, proof2Page, proof1Page, sedPage, proof4Page, proof3Page, feedbackPage, sendPage));
      Tool keyTool = evaluationForm.getEvaluation().getTool(UnderstandingProofAttemptsEvaluation.KEY_TOOL_NAME);
      Tool sedTool = evaluationForm.getEvaluation().getTool(UnderstandingProofAttemptsEvaluation.SED_TOOL_NAME);
      evaluationFormInput.setTool(proof2Page, keyTool);
      evaluationFormInput.setTool(proof1Page, keyTool);
      evaluationFormInput.setTool(proof4Page, sedTool);
      evaluationFormInput.setTool(proof3Page, sedTool);
      return CollectionUtil.toList(evaluationFormInput);
   }
}
