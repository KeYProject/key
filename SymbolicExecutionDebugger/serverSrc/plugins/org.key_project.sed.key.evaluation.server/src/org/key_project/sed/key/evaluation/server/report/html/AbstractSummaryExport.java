package org.key_project.sed.key.evaluation.server.report.html;

import java.util.List;
import java.util.Map.Entry;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.SectionQuestion;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.FilteredStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.StringUtil;

/**
 * Provides the basic functionality to export summaries.
 * @author Martin Hentschel
 */
public abstract class AbstractSummaryExport implements IHTMLSectionAppender {
   protected String createValueLatex(AbstractQuestion question, String idPrefix, EvaluationResult result) {
      StringBuffer latex = new StringBuffer();
      latex.append("\\newcounter{" + idPrefix + "FeedbackRowcount}" + StringUtil.NEW_LINE);
      latex.append("\\setcounter{" + idPrefix + "FeedbackRowcount}{0}" + StringUtil.NEW_LINE);
      latex.append("\\newcommand{\\" + idPrefix + "FeedbackRowcountautorefname}{ID}" + StringUtil.NEW_LINE);
      latex.append("\\begin{tabularx}{1.0\\textwidth}{lX}" + StringUtil.NEW_LINE);
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      latex.append("ID & Feedback\\\\" + StringUtil.NEW_LINE);
      latex.append("\\midrule" + StringUtil.NEW_LINE);
      boolean afterFirst = false;
      int i = 1;
      for (Entry<String, EvaluationAnswers> entry : result.getIdInputMap().entrySet()) {
         List<QuestionInput> inputs = entry.getValue().getQuestionInputs(question);
         if (inputs != null && inputs.size() == 1) {
            String value = inputs.get(0).getValue();
            if (!StringUtil.isTrimmedEmpty(value)) {
               if (afterFirst) {
                  latex.append("\\midrule" + StringUtil.NEW_LINE);
               }
               else {
                  afterFirst = true;
               }
               latex.append(i + "\\refstepcounter{" + idPrefix + "FeedbackRowcount}\\label{row:" + idPrefix + entry.getKey() + "} & ``" + value + "''\\\\" + StringUtil.NEW_LINE);
               i++;
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

   protected String createQuestionLatex(AbstractChoicesQuestion choiceQuestion, Statistics statistics, String experienceLabel) {
      StringBuffer latex = new StringBuffer();
      latex.append("\\begin{tabular}{lrrrr}" + StringUtil.NEW_LINE);
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      latex.append("& \\multicolumn{4}{c}{" + experienceLabel + "}\\\\" + StringUtil.NEW_LINE);
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
