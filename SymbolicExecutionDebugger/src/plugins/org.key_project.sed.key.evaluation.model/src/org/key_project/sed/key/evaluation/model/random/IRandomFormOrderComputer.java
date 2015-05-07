package org.key_project.sed.key.evaluation.model.random;

import java.util.List;

import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;

public interface IRandomFormOrderComputer {
   public List<RandomFormInput> updateRandomOrder(EvaluationInput evaluationInput, AbstractFormInput<?> currentForm);
}
