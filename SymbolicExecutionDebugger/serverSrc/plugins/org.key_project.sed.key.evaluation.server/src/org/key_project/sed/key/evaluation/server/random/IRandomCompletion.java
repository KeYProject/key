package org.key_project.sed.key.evaluation.server.random;

import java.util.List;

import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.RandomFormInput;

public interface IRandomCompletion {
   public List<RandomFormInput> computeRandomValues(EvaluationInput evaluationInput, AbstractFormInput<?> currentForm);
}
