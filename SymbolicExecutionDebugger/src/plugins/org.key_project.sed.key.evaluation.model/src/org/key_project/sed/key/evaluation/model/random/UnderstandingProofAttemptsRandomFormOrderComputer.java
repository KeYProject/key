package org.key_project.sed.key.evaluation.model.random;

import java.util.List;

import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;
import org.key_project.util.java.CollectionUtil;

public class UnderstandingProofAttemptsRandomFormOrderComputer implements IRandomFormOrderComputer {
   @SuppressWarnings("unchecked")
   @Override
   // TODO: Compute a real random order!
   public List<RandomFormInput> updateRandomOrder(EvaluationInput evaluationInput, AbstractFormInput<?> currentForm) {
      RandomForm evaluationForm = ((UnderstandingProofAttemptsEvaluation) evaluationInput.getEvaluation()).getEvaluationForm();
      RandomFormInput evaluationFormInput = (RandomFormInput) evaluationInput.getFormInput(evaluationForm);
      AbstractPageInput<?>[] pageInputs = evaluationFormInput.getPageInputs();
      evaluationFormInput.setPageOrder(CollectionUtil.toList(pageInputs[1], pageInputs[0], pageInputs[3], pageInputs[2], pageInputs[4]));
      return CollectionUtil.toList(evaluationFormInput);
   }

}
