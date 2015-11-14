package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.SectionQuestion;
import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.FilteredStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

/**
 * Exports the results of the summary page as LaTeX file.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsSummaryExport implements IHTMLSectionAppender {
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
      String keyVsSed = createQuestionLatex(keyVsSedQuestion, statistics);
      String feedback = createValueLatex(feedbackQuestion, result);
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

   protected String createValueLatex(AbstractQuestion question, EvaluationResult result) {
      StringBuffer latex = new StringBuffer();
      latex.append("\\begin{tabularx}{1.0\\textwidth}{X}" + StringUtil.NEW_LINE);
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      boolean afterFirst = false;
      for (EvaluationAnswers answer : result.getIdInputMap().values()) {
         List<QuestionInput> inputs = answer.getQuestionInputs(question);
         if (inputs != null && inputs.size() == 1) {
            String value = inputs.get(0).getValue();
            if (!StringUtil.isTrimmedEmpty(value)) {
               if (afterFirst) {
                  latex.append("\\midrule" + StringUtil.NEW_LINE);
               }
               else {
                  afterFirst = true;
               }
               latex.append("``" + value + "''\\\\");
            }
         }
      }
      latex.append("\\bottomrule" + StringUtil.NEW_LINE);
      latex.append("\\end{tabularx}" + StringUtil.NEW_LINE);
      return latex.toString();
   }

   protected String createSingleFeatureLatex(SectionQuestion sectionQuestion, IStatisticsFilter filter, Statistics statistics) {
      StringBuffer latex = new StringBuffer();
      latex.append("\\begin{tabular}{lrrrrr}" + StringUtil.NEW_LINE);
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      latex.append("& \\rotatebox{90}{Very Helpful~(\\%)} & \\rotatebox{90}{Helpful~(\\%)} & \\rotatebox{90}{Little Helpful~(\\%)} & \\rotatebox{90}{Not Helpful~(\\%)} & \\rotatebox{90}{Never Used~(\\%)}\\\\" + StringUtil.NEW_LINE);
      latex.append("\\midrule" + StringUtil.NEW_LINE);
      appendSingleFeatureChildQuestion(sectionQuestion, filter, statistics, latex);
      latex.append("\\bottomrule" + StringUtil.NEW_LINE);
      latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
      return latex.toString();
   }
   
   protected void appendSingleFeatureChildQuestion(SectionQuestion sectionQuestion, IStatisticsFilter filter, Statistics statistics, StringBuffer latex) {
      for (AbstractQuestion question : sectionQuestion.getChildQuestions()) {
         if (question instanceof AbstractChoicesQuestion) {
            AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
            latex.append(question.getLatexLabel());
            for (Choice choice : choiceQuestion.getChoices()) {
               FilteredStatistics fs = statistics.getFilteredStatistics(filter);
               latex.append(" & " + fs.computeChoicePercent(choiceQuestion, choice));
            }
            latex.append("\\\\" + StringUtil.NEW_LINE);
         }
      }
   }

   protected String createQuestionLatex(AbstractChoicesQuestion choiceQuestion, Statistics statistics) {
      StringBuffer latex = new StringBuffer();
      latex.append("\\begin{tabular}{lrrrr}" + StringUtil.NEW_LINE);
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      latex.append("& \\multicolumn{4}{c}{\\KeY experience}\\\\" + StringUtil.NEW_LINE);
      for (IStatisticsFilter filter : statistics.getFilters()) {
         latex.append("&\\rotatebox{90}{" + filter.getLatexName() + "~(\\%)}");
      }
      latex.append("\\\\" + StringUtil.NEW_LINE);
      latex.append("\\midrule" + StringUtil.NEW_LINE);
      for (Choice choice : choiceQuestion.getChoices()) {
         latex.append(choice.getLatexText());
         for (IStatisticsFilter filter : statistics.getFilters()) {
            FilteredStatistics fs = statistics.getFilteredStatistics(filter);
            latex.append(" & " + fs.computeChoicePercent(choiceQuestion, choice));
         }
         latex.append("\\\\" + StringUtil.NEW_LINE);
      }
      latex.append("\\bottomrule" + StringUtil.NEW_LINE);
      latex.append("\\end{tabular}" + StringUtil.NEW_LINE);
      return latex.toString();
   }

   protected String createFeatureLatex(SectionQuestion sectionQuestion, Statistics statistics) {
      StringBuffer latex = new StringBuffer();
      latex.append("\\begin{tabularx}{1.0\\textwidth}{Xrrrrrrrrrrrrrrrrrrrr}" + StringUtil.NEW_LINE);
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      latex.append("& \\multicolumn{4}{c}{Very Helpful} & \\multicolumn{4}{c}{Helpful} & \\multicolumn{4}{c}{Little Helpful} & \\multicolumn{4}{c}{Not Helpful} & \\multicolumn{4}{c}{Never Used}\\\\" + StringUtil.NEW_LINE);
      for (int i = 0; i < 5; i++) {
         for (IStatisticsFilter filter : statistics.getFilters()) {
            latex.append("&\\rotatebox{90}{" + filter.getLatexName() + "}");
         }
      }
      latex.append("\\\\" + StringUtil.NEW_LINE);
      latex.append("\\midrule" + StringUtil.NEW_LINE);
      appendFeatureChildQuestion(sectionQuestion, statistics, latex);
      latex.append("\\bottomrule" + StringUtil.NEW_LINE);
      latex.append("\\end{tabularx}" + StringUtil.NEW_LINE);
      return latex.toString();
   }
   
   protected void appendFeatureChildQuestion(SectionQuestion sectionQuestion, Statistics statistics, StringBuffer latex) {
      for (AbstractQuestion question : sectionQuestion.getChildQuestions()) {
         if (question instanceof AbstractChoicesQuestion) {
            AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
            latex.append(question.getLatexLabel());
            for (Choice choice : choiceQuestion.getChoices()) {
               for (IStatisticsFilter filter : statistics.getFilters()) {
                  FilteredStatistics fs = statistics.getFilteredStatistics(filter);
                  latex.append(" & " + fs.computeChoicePercent(choiceQuestion, choice));
               }
            }
            latex.append("\\\\" + StringUtil.NEW_LINE);
         }
      }
   }
}
