package org.key_project.sed.key.evaluation.server.report.filter;

import java.util.List;

import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.QuestionPageInput;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;

/**
 * An {@link IStatisticsFilter} used in the {@link UnderstandingProofAttemptsEvaluation}
 * to filter answers by the KeY experience.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsKeYExperienceFilter extends AbstractStatisticsFilter {
   /**
    * The {@link Choice} with the KeY experience of interest.
    */
   private final Choice choice;

   /**
    * Constructor.
    * @param choice The {@link Choice} with the KeY experience of interest.
    */
   public UnderstandingProofAttemptsKeYExperienceFilter(Choice choice) {
      this.choice = choice;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return choice.getText();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getLatexName() {
      if (UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE.equals(choice.getValue())) {
         return "None";
      }
      else if (UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE.equals(choice.getValue())) {
         return "$<$ 2 y.";
      }
      else if (UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE.equals(choice.getValue())) {
         return "$\\geq$ 2 y.";
      }
      else {
         return getName();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean accept(EvaluationAnswers answer) {
      List<AbstractFormInput<?>> formInputs = answer.getFormInputs(UnderstandingProofAttemptsEvaluation.INSTANCE.getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME));
      if (formInputs != null && formInputs.size() == 1) {
         AbstractFormInput<?> introductionFormInput = formInputs.get(0);
         QuestionPageInput backgroundPageInput = (QuestionPageInput) introductionFormInput.getPageInput(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
         QuestionInput questionInput = backgroundPageInput.getQuestionInput(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
         return questionInput.isChoiceSelected(choice);
      }
      else {
         return false;
      }
   }
}
