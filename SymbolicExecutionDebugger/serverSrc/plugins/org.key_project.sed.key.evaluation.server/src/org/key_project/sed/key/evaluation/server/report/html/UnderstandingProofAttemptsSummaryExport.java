package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.SectionQuestion;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.IOUtil;

/**
 * Exports the results of the summary page as LaTeX file.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsSummaryExport extends AbstractSummaryExport {
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, 
                                                   AbstractEvaluation evaluation, 
                                                   EvaluationResult result, 
                                                   Statistics statistics, 
                                                   StringBuffer sb) {
      // Get needed questions
      AbstractForm evaluationForm = evaluation.getForm(UnderstandingProofAttemptsEvaluation.EVALUATION_FORM_NAME);
      QuestionPage feedbackPage = (QuestionPage) evaluationForm.getPage(UnderstandingProofAttemptsEvaluation.FEEDBACK_PAGE);
      SectionQuestion keySection = (SectionQuestion) feedbackPage.getQuestion(UnderstandingProofAttemptsEvaluation.KEY_FEEDBACK_SECTION);
      SectionQuestion sedSection = (SectionQuestion) feedbackPage.getQuestion(UnderstandingProofAttemptsEvaluation.SED_FEEDBACK_SECTION);
      SectionQuestion keyVsSedSection = (SectionQuestion) feedbackPage.getQuestion(UnderstandingProofAttemptsEvaluation.KEY_VS_SED_FEEDBACK_SECTION);
      SectionQuestion feedbackSection = (SectionQuestion) feedbackPage.getQuestion(UnderstandingProofAttemptsEvaluation.FEEDBACK_SECTION);
      AbstractChoicesQuestion keyVsSedQuestion = (AbstractChoicesQuestion) keyVsSedSection.getChildQuestions()[0];
      AbstractQuestion feedbackQuestion = feedbackSection.getChildQuestions()[0];
      // Crate Latex file
      String keyFeatures = createFeatureLatex(keySection, statistics);
      String sedFeatures = createFeatureLatex(sedSection, statistics);
      String keyVsSed = createQuestionLatex(keyVsSedQuestion, statistics, "\\KeY experience");
      String feedback = createValueLatex(feedbackQuestion, "upa", result);
      List<AdditionalFile> additionalFiles = new LinkedList<AdditionalFile>();
      additionalFiles.add(new AdditionalFile("_KeY_Features.tex", keyFeatures.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_SED_Features.tex", sedFeatures.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_KeY_vs_SED.tex", keyVsSed.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      for (IStatisticsFilter filter : statistics.getFilters()) {
         String key = createSingleFeatureLatex(keySection, filter, statistics);
         String sed = createSingleFeatureLatex(sedSection, filter, statistics);
         additionalFiles.add(new AdditionalFile("_KeY_Features_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", key.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
         additionalFiles.add(new AdditionalFile("_SED_Features_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", sed.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      }
      additionalFiles.add(new AdditionalFile("_Feedback.tex", feedback.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      return additionalFiles;
   }
}
