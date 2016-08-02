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
import org.key_project.sed.key.evaluation.model.definition.ReviewingCodeEvaluation;
import org.key_project.sed.key.evaluation.model.definition.SectionQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.IOUtil;

/**
 * Exports the results of the summary page as LaTeX file.
 * @author Martin Hentschel
 */
public class ReviewingCodeSummaryExport extends AbstractSummaryExport {
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, 
                                                   AbstractEvaluation evaluation, 
                                                   EvaluationResult result, 
                                                   Statistics statistics, 
                                                   StringBuffer sb) {
      // Get tools
      Tool sedTool = evaluation.getTool(ReviewingCodeEvaluation.SED_TOOL_NAME);
      // Get needed questions
      AbstractForm evaluationForm = evaluation.getForm(ReviewingCodeEvaluation.EVALUATION_FORM_NAME);
      QuestionPage feedbackPage = (QuestionPage) evaluationForm.getPage(ReviewingCodeEvaluation.FEEDBACK_PAGE);
      SectionQuestion sedSection = (SectionQuestion) feedbackPage.getQuestion(ReviewingCodeEvaluation.SED_FEEDBACK_SECTION);
      SectionQuestion dcrVsSedSection = (SectionQuestion) feedbackPage.getQuestion(ReviewingCodeEvaluation.DCR_VS_SED_FEEDBACK_SECTION);
      SectionQuestion feedbackSection = (SectionQuestion) feedbackPage.getQuestion(ReviewingCodeEvaluation.FEEDBACK_SECTION);
      AbstractChoicesQuestion dcrVsSedQuestion = (AbstractChoicesQuestion) dcrVsSedSection.getChildQuestions()[0];
      AbstractQuestion feedbackQuestion = feedbackSection.getChildQuestions()[0];
      // Crate Latex files
      String sedFeatures = createFeatureLatex(sedSection, statistics);
      String dcrVsSed = createQuestionLatex(dcrVsSedQuestion, statistics, "\\Java experience");
      String feedback = createValueLatex(feedbackQuestion, "rc", result);
      List<AdditionalFile> additionalFiles = new LinkedList<AdditionalFile>();
      additionalFiles.add(new AdditionalFile("_SED_Features.tex", sedFeatures.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_DCR_vs_SED.tex", dcrVsSed.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      for (IStatisticsFilter filter : statistics.getFilters()) {
         String sed = createSingleFeatureLatex(sedSection, filter, statistics);
         additionalFiles.add(new AdditionalFile("_SED_Features_" + IOUtil.validateOSIndependentFileName(filter.getName()) + ".tex", sed.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      }
      additionalFiles.add(new AdditionalFile("_Feedback.tex", feedback.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      // Create HTML files
      String sedFeaturesHtml = createFeatureHtml(sedSection, statistics, "Java experience", sedTool.getName());
      String dcrVsSedHtml = createQuestionHtml(dcrVsSedQuestion, statistics, "Java experience");
      additionalFiles.add(new AdditionalFile("_SED_Features.html", sedFeaturesHtml.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      additionalFiles.add(new AdditionalFile("_DCR_vs_SED.html", dcrVsSedHtml.toString().getBytes(IOUtil.DEFAULT_CHARSET)));
      return additionalFiles;
   }
}
