package org.key_project.sed.key.evaluation.server.report;

import java.util.HashMap;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.util.java.StringUtil;

/**
 * Provides the results of an evaluation.
 * @author Martin Hentschel
 */
public class EvaluationResult {
   /**
    * The available {@link EvaluationAnswers}.
    */
   private final Map<String, EvaluationAnswers> idInputMap = new HashMap<String, EvaluationAnswers>();

   /**
    * Analyzes the given {@link EvaluationInput}.
    * @param form The {@link AbstractFormInput} to analyze.
    * @param input The {@link EvaluationInput} to anaylze.
    */
   protected void addEvaluationInput(AbstractForm form, EvaluationInput input) {
      assert !StringUtil.isTrimmedEmpty(input.getUUID());
      EvaluationAnswers answers = idInputMap.get(input.getUUID());
      if (answers == null) {
         answers = new EvaluationAnswers();
         idInputMap.put(input.getUUID(), answers);
      }
      answers.addFormInput(input.getFormInput(form));
   }

   /**
    * Returns the available {@link EvaluationAnswers}.
    * @return The available {@link EvaluationAnswers}.
    */
   public Map<String, EvaluationAnswers> getIdInputMap() {
      return idInputMap;
   }
}