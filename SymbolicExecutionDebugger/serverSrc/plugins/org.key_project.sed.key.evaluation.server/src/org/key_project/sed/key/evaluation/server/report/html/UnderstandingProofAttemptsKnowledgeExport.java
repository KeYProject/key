package org.key_project.sed.key.evaluation.server.report.html;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.util.java.IOUtil;

/**
 * Creates a CSV file with the participants experience.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsKnowledgeExport extends AbstractKnowledgeExport {
   @Override
   protected AbstractForm getEvaluationForm(AbstractEvaluation evaluation) {
      return evaluation.getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME);
   }

   @Override
   protected QuestionDefinition[] getQuestions(AbstractEvaluation evaluation) {
      AbstractForm introductionForm = evaluation.getForm(UnderstandingProofAttemptsEvaluation.INTRODUCTION_FORM_NAME);
      QuestionPage backgroundPage = (QuestionPage) introductionForm.getPage(UnderstandingProofAttemptsEvaluation.BACKGROUND_PAGE_NAME);
      AbstractQuestion javaQuestion = backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_JAVA_QUESTION_NAME);
      AbstractQuestion jmlQuestion = backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_JML_QUESTION_NAME);
      AbstractQuestion keyQuestion = backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME);
      AbstractQuestion sedQuestion = backgroundPage.getQuestion(UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME);
      return new QuestionDefinition[] {new QuestionDefinition(javaQuestion, UnderstandingProofAttemptsEvaluation.JAVA_EXPERIENCE_NON_VALUE, UnderstandingProofAttemptsEvaluation.JAVA_EXPERIENCE_LESS_THAN_2_YEARS_VALUE, UnderstandingProofAttemptsEvaluation.JAVA_EXPERIENCE_MORE_THAN_2_YEARS_VALUE, "Java"),
                                       new QuestionDefinition(jmlQuestion, UnderstandingProofAttemptsEvaluation.JML_EXPERIENCE_NON_VALUE, UnderstandingProofAttemptsEvaluation.JML_EXPERIENCE_LESS_THAN_2_YEARS_VALUE, UnderstandingProofAttemptsEvaluation.JML_EXPERIENCE_MORE_THAN_2_YEARS_VALUE, "JML"),
                                       new QuestionDefinition(keyQuestion, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_NON_VALUE, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_LESS_THAN_2_YEARS_VALUE, UnderstandingProofAttemptsEvaluation.KEY_EXPERIENCE_MORE_THAN_2_YEARS_VALUE, "KeY"),
                                       new QuestionDefinition(sedQuestion, UnderstandingProofAttemptsEvaluation.SED_EXPERIENCE_NON_VALUE, UnderstandingProofAttemptsEvaluation.SED_EXPERIENCE_LESS_THAN_1_YEAR_VALUE, UnderstandingProofAttemptsEvaluation.SED_EXPERIENCE_MORE_THAN_1_YEAR_VALUE, "SED")};
   }

   @Override
   protected String computeLatexFileName(IStatisticsFilter filter) {
      return "_Knowledge_KeY_SED_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex";
   }

   @Override
   protected NestedChoiceSummary updateNestedChoiceNone(NestedChoiceSummary current, QuestionInput qi) {
      if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getNone();
      }
      else if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getNone();
      }
      else {
         return super.updateNestedChoiceNone(current, qi);
      }
   }

   @Override
   protected NestedChoiceSummary updateNestedChoiceLess(NestedChoiceSummary current, QuestionInput qi) {
      if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getLess();
      }
      else if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getLess();
      }
      else {
         return super.updateNestedChoiceLess(current, qi);
      }
   }

   @Override
   protected NestedChoiceSummary updateNestedChoiceMore(NestedChoiceSummary current, QuestionInput qi) {
      if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_KEY_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getMore();
      }
      else if (UnderstandingProofAttemptsEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getMore();
      }
      else {
         return super.updateNestedChoiceMore(current, qi);
      }
   }

   @Override
   protected String getNestedChoiceColumnHeader() {
      return "\\SED";
   }

   @Override
   protected String getNestedChoiceRowHeader() {
      return "\\KeY";
   }
}
