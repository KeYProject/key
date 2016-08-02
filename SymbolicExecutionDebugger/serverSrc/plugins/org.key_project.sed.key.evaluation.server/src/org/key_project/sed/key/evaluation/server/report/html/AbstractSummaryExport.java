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

   protected String createFeatureHtml(SectionQuestion sectionQuestion, Statistics statistics, String experienceLabel, String toolName) {
      StringBuffer html = new StringBuffer();
      html.append("<table border=\"0\" cellpadding=\"3\" cellspacing=\"2\">" + StringUtil.NEW_LINE);
      html.append("<tr style=\"background-color: #4e9ad6;font-weight: bold;\">" + StringUtil.NEW_LINE);
      html.append("<td rowspan=\"3\" colspan=\"2\">&nbsp;</td>" + StringUtil.NEW_LINE);
      html.append("<td colspan=\"20\">" + experienceLabel + "</td>" + StringUtil.NEW_LINE);
      html.append("</tr>" + StringUtil.NEW_LINE);
      html.append("<tr style=\"background-color: #4e9ad6;font-weight: bold;\">" + StringUtil.NEW_LINE);
      for (IStatisticsFilter filter : statistics.getFilters()) {
         html.append("<td colspan=\"5\">" + filter.getName() + "</td>" + StringUtil.NEW_LINE);
      }
      html.append("</tr>" + StringUtil.NEW_LINE);
      html.append("<tr style=\"background-color: #4e9ad6;font-weight: bold;\">" + StringUtil.NEW_LINE);
      for (@SuppressWarnings("unused") IStatisticsFilter filter : statistics.getFilters()) {
         html.append("<td>Very Helpful (%)</td>" + StringUtil.NEW_LINE);
         html.append("<td>Helpful (%)</td>" + StringUtil.NEW_LINE);
         html.append("<td>Somewhat Helpful (%)</td>" + StringUtil.NEW_LINE);
         html.append("<td>Not Helpful (%)</td>" + StringUtil.NEW_LINE);
         html.append("<td>Never Used (%)</td>" + StringUtil.NEW_LINE);
      }
      html.append("</tr>" + StringUtil.NEW_LINE);
      appendFeatureChildQuestionHtml(sectionQuestion, statistics, toolName, html);
      html.append("</table>" + StringUtil.NEW_LINE);
      return html.toString();
   }
   
   protected void appendFeatureChildQuestionHtml(SectionQuestion sectionQuestion, Statistics statistics, String toolName, StringBuffer html) {
      boolean first = true;
      for (AbstractQuestion question : sectionQuestion.getChildQuestions()) {
         if (question instanceof AbstractChoicesQuestion) {
            html.append("<tr style=\"background-color: #b1d3ec;\">" + StringUtil.NEW_LINE);
            if (first) {
               html.append("<td rowspan=\"" + sectionQuestion.countChildQuestions() + "\">" + toolName + "</td>" + StringUtil.NEW_LINE);
               first = false;
            }
            AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
            html.append("<td>" + question.getLatexLabel() + "</td>" + StringUtil.NEW_LINE);
            for (Choice choice : choiceQuestion.getChoices()) {
               for (IStatisticsFilter filter : statistics.getFilters()) {
                  FilteredStatistics fs = statistics.getFilteredStatistics(filter);
                  html.append("<td>" + fs.computeChoicePercent(choiceQuestion, choice) + "</td>" + StringUtil.NEW_LINE);
               }
            }
            html.append("</tr>" + StringUtil.NEW_LINE);
         }
      }
   }

   protected String createQuestionHtml(AbstractChoicesQuestion choiceQuestion, Statistics statistics, String experienceLabel) {
      StringBuffer html = new StringBuffer();
      html.append("<table border=\"0\" cellpadding=\"3\" cellspacing=\"2\">" + StringUtil.NEW_LINE);
      html.append("<tr style=\"background-color: #4e9ad6;font-weight: bold;\">" + StringUtil.NEW_LINE);
      html.append("<td rowspan=\"2\">&nbsp;</td>" + StringUtil.NEW_LINE);
      html.append("<td colspan=\"5\">" + experienceLabel + "</td>" + StringUtil.NEW_LINE);
      html.append("</tr>" + StringUtil.NEW_LINE);
      html.append("<tr style=\"background-color: #4e9ad6;font-weight: bold;\">" + StringUtil.NEW_LINE);
      for (IStatisticsFilter filter : statistics.getFilters()) {
         html.append("<td>" + filter.getName() + "</td>" + StringUtil.NEW_LINE);
      }
      html.append("</tr>" + StringUtil.NEW_LINE);
      for (Choice choice : choiceQuestion.getChoices()) {
         html.append("<tr style=\"background-color: #b1d3ec;\">" + StringUtil.NEW_LINE);
         html.append("<td>" + choice.getLatexText() + "</td>" + StringUtil.NEW_LINE);
         for (IStatisticsFilter filter : statistics.getFilters()) {
            FilteredStatistics fs = statistics.getFilteredStatistics(filter);
            html.append("<td>" + fs.computeChoicePercent(choiceQuestion, choice) + "</td>" + StringUtil.NEW_LINE);
         }
         html.append("</tr>" + StringUtil.NEW_LINE);
      }
      html.append("</table>" + StringUtil.NEW_LINE);
      return html.toString();
   }
}
