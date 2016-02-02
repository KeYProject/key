package org.key_project.sed.key.evaluation.server.report.html;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.ReviewingCodeEvaluation;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.util.java.IOUtil;

/**
 * Creates a CSV file with the participants experience.
 * @author Martin Hentschel
 */
public class ReviewingCodeKnowledgeExport extends AbstractKnowledgeExport {
   @Override
   protected AbstractForm getEvaluationForm(AbstractEvaluation evaluation) {
      return evaluation.getForm(ReviewingCodeEvaluation.EVALUATION_FORM_NAME);
   }

   @Override
   protected QuestionDefinition[] getQuestions(AbstractEvaluation evaluation) {
      AbstractForm introductionForm = evaluation.getForm(ReviewingCodeEvaluation.INTRODUCTION_FORM_NAME);
      QuestionPage backgroundPage = (QuestionPage) introductionForm.getPage(ReviewingCodeEvaluation.BACKGROUND_PAGE_NAME);
      AbstractQuestion javaQuestion = backgroundPage.getQuestion(ReviewingCodeEvaluation.EXPERIENCE_WITH_JAVA_QUESTION_NAME);
      AbstractQuestion jmlQuestion = backgroundPage.getQuestion(ReviewingCodeEvaluation.EXPERIENCE_WITH_JML_QUESTION_NAME);
      AbstractQuestion keyQuestion = backgroundPage.getQuestion(ReviewingCodeEvaluation.EXPERIENCE_WITH_SE_QUESTION_NAME);
      AbstractQuestion sedQuestion = backgroundPage.getQuestion(ReviewingCodeEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME);
      return new QuestionDefinition[] {new QuestionDefinition(javaQuestion, ReviewingCodeEvaluation.JAVA_EXPERIENCE_NON_VALUE, ReviewingCodeEvaluation.JAVA_EXPERIENCE_LESS_THAN_2_YEARS_VALUE, ReviewingCodeEvaluation.JAVA_EXPERIENCE_MORE_THAN_2_YEARS_VALUE, "Java"),
                                       new QuestionDefinition(jmlQuestion, ReviewingCodeEvaluation.JML_EXPERIENCE_NON_VALUE, ReviewingCodeEvaluation.JML_EXPERIENCE_LESS_THAN_2_YEARS_VALUE, ReviewingCodeEvaluation.JML_EXPERIENCE_MORE_THAN_2_YEARS_VALUE, "JML"),
                                       new QuestionDefinition(keyQuestion, ReviewingCodeEvaluation.SE_EXPERIENCE_NON_VALUE, ReviewingCodeEvaluation.SE_EXPERIENCE_LESS_THAN_2_YEARS_VALUE, ReviewingCodeEvaluation.SE_EXPERIENCE_MORE_THAN_2_YEARS_VALUE, "SE"),
                                       new QuestionDefinition(sedQuestion, ReviewingCodeEvaluation.SED_EXPERIENCE_NON_VALUE, ReviewingCodeEvaluation.SED_EXPERIENCE_LESS_THAN_1_YEAR_VALUE, ReviewingCodeEvaluation.SED_EXPERIENCE_MORE_THAN_1_YEAR_VALUE, "SED")};
   }

   @Override
   protected String computeLatexFileName(IStatisticsFilter filter) {
      return "_Knowledge_Java_SED_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex";
   }

   @Override
   protected NestedChoiceSummary updateNestedChoiceNone(NestedChoiceSummary current, QuestionInput qi) {
      if (ReviewingCodeEvaluation.EXPERIENCE_WITH_JAVA_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getNone();
      }
      else if (ReviewingCodeEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getNone();
      }
      else {
         return super.updateNestedChoiceNone(current, qi);
      }
   }

   @Override
   protected NestedChoiceSummary updateNestedChoiceLess(NestedChoiceSummary current, QuestionInput qi) {
      if (ReviewingCodeEvaluation.EXPERIENCE_WITH_JAVA_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getLess();
      }
      else if (ReviewingCodeEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getLess();
      }
      else {
         return super.updateNestedChoiceLess(current, qi);
      }
   }

   @Override
   protected NestedChoiceSummary updateNestedChoiceMore(NestedChoiceSummary current, QuestionInput qi) {
      if (ReviewingCodeEvaluation.EXPERIENCE_WITH_JAVA_QUESTION_NAME.equals(qi.getQuestion().getName())) {
         return current.getMore();
      }
      else if (ReviewingCodeEvaluation.EXPERIENCE_WITH_SED_QUESTION_NAME.equals(qi.getQuestion().getName())) {
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
      return "\\Java";
   }
}
