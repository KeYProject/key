package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.IQuestionWithCildren;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.FilteredStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.PageStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.QuestionStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;

/**
 * Appends the tool comparison section.
 * @author Martin Hentschel
 */
public class HTMLToolSectionAppender implements IHTMLSectionAppender {
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, AbstractEvaluation evaluation, EvaluationResult result, Statistics statistics, StringBuffer sb) {
      sb.append("<h1><a name=\"statistics\">Tool Comparison</a></h1>");
      sb.append("<table border=\"1\">");
      // Append header
      sb.append("<tr>");
      sb.append("<td rowspan=\"3\" colspan=\"3\">&nbsp;</td>");
      for (IStatisticsFilter filter : statistics.getFilters()) {
         sb.append("<td colspan=\"" + ((evaluation.getTools().length) * 8) + "\" align=\"center\"><b>");
         sb.append(filter.getName());
         FilteredStatistics fs = statistics.getFilteredStatistics(filter);
         sb.append(" (");
         sb.append(fs.getAnswersCount());
         sb.append(" answers)");
         sb.append("</b></td>");
      }
      sb.append("</tr>");
      sb.append("<tr>");
      for (@SuppressWarnings("unused") IStatisticsFilter filter : statistics.getFilters()) {
         for (Tool tool : evaluation.getTools()) {
            sb.append("<td colspan=\"8\" align=\"center\"><b>");
            sb.append(tool.getName());
            sb.append("</b></td>");
         }
      }
      sb.append("</tr>");
      sb.append("<tr>");
      for (@SuppressWarnings("unused") IStatisticsFilter filter : statistics.getFilters()) {
         for (@SuppressWarnings("unused") Tool tool : evaluation.getTools()) {
            appendQuestionHeaders(sb);
         }
      }
      sb.append("</tr>");
      // Append content
      for (AbstractForm form : evaluation.getForms()) {
         Map<AbstractPage, Integer> questionCount = countStatistics(statistics, form);
         int formSpan = 0;
         int formPagesSpan = 0;
         for (Integer value : questionCount.values()) {
            if (value > 0) {
               formPagesSpan++;
            }
            formSpan += value;
         }
         if (formSpan > 0) {
            sb.append("<tr>");
            sb.append("<td rowspan=\"" + (2 + formSpan + formPagesSpan) + "\" valign=\"top\"><b>");
            sb.append(form.getName());
            sb.append("</b></td>");
            sb.append("<td colspan=\"" + (2 + ((evaluation.getTools().length) * 8 * statistics.getFilters().length)) + "\">&nbsp;</td>");
            sb.append("</tr>");
            for (AbstractPage page : form.getPages()) {
               int pageSpan = questionCount.get(page);
               if (pageSpan > 0) {
                  sb.append("<tr>");
                  sb.append("<td rowspan=\"" + (pageSpan + 1) + "\" valign=\"top\"><b>");
                  sb.append(page.getName());
                  sb.append("</b></td>");
                  sb.append("<td>&nbsp;</td>");
                  for (IStatisticsFilter filter : statistics.getFilters()) {
                     FilteredStatistics fs = statistics.getFilteredStatistics(filter);
                     Set<Tool> winningTimesTools = fs.computeWinningPageTimeTools(page);
                     for (Tool tool : evaluation.getTools()) {
                        PageStatistics ps = fs.getPageStatistics(tool, page);
                        sb.append("<td colspan=\"3\">&nbsp;</td>");
                        if (ps != null) {
                           if (winningTimesTools != null && winningTimesTools.contains(tool)) {
                              String color = winningTimesTools.size() == 1 ?
                                             "blue" :
                                             "#FF00FF";
                              sb.append("<td align=\"right\"><font color=\"" + color + "\">");
                              sb.append(ps.computeAverageTime());
                              sb.append("&nbsp;ms</font></td>");
                           }
                           else {
                              sb.append("<td align=\"right\">");
                              sb.append(ps.computeAverageTime());
                              sb.append("&nbsp;ms</td>");
                           }
                        }
                        else {
                           sb.append("<td>&nbsp;</td>");
                        }
                        sb.append("<td colspan=\"4\">&nbsp;</td>");
                     }
                  }
                  sb.append("</tr>");
                  if (page instanceof QuestionPage) {
                     QuestionPage questionPage = (QuestionPage) page;
                     for (AbstractQuestion question : questionPage.getQuestions()) {
                        appendQuestion(evaluation, statistics, question, sb);
                     }
                  }
                  else {
                     throw new IllegalStateException("Unsupported page: " + page);
                  }
               }
            }
            // Append all together
            sb.append("<tr>");
            sb.append("<td colspan=\"2\"><b>All Together</b></td>");
            for (IStatisticsFilter filter : statistics.getFilters()) {
               FilteredStatistics fs = statistics.getFilteredStatistics(filter);
               Map<Tool, QuestionStatistics> questionStatistics = new HashMap<Tool, QuestionStatistics>();
               for (Tool tool : evaluation.getTools()) {
                  questionStatistics.put(tool, fs.computeAllTogetherQuestionStatistics(tool));
               }
               for (Tool tool : evaluation.getTools()) {
                  appendQuestionValues(questionStatistics.get(tool), 
                                       FilteredStatistics.computeWinningCorrectTools(questionStatistics), 
                                       FilteredStatistics.computeWinningCorrectTrustTools(questionStatistics), 
                                       FilteredStatistics.computeWinningTimeTools(questionStatistics), 
                                       FilteredStatistics.computeWinningTrustTimeTools(questionStatistics), 
                                       FilteredStatistics.computeWinningTrustScoreTools(questionStatistics), 
                                       tool, 
                                       true, 
                                       sb);
               }
            }
            sb.append("</tr>");
         }
      }
      sb.append("</table>");
      if (statistics.isMultipleValuedAnswersIgnored()) {
         sb.append("<p><a href=\"#answers\">Answers with multiple values (gray colored) are ignored.</a></p>");
      }
      return null;
   }
   
   /**
    * Appends the tool static question headers.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendQuestionHeaders(StringBuffer sb) {
      sb.append("<td align=\"center\"><b>Correct</b></td>");
      sb.append("<td align=\"center\"><b>Wrong</b></td>");
      sb.append("<td align=\"center\"><b>Correctness Score</b></td>");
      sb.append("<td align=\"center\"><b>Average Time</b></td>");
      sb.append("<td align=\"center\"><b>Trust Correct</b></td>");
      sb.append("<td align=\"center\"><b>Trust Wrong</b></td>");
      sb.append("<td align=\"center\"><b>Trust Score</b></td>");
      sb.append("<td align=\"center\"><b>Average Trust Time</b></td>");
   }

   /**
    * Appends the tool statistics of the given {@link AbstractQuestion}.
    * @param evaluation The analyzed {@link AbstractEvaluation}.
    * @param statistics The computed {@link Statistics}.
    * @param question The {@link AbstractQuestion} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendQuestion(AbstractEvaluation evaluation, Statistics statistics, AbstractQuestion question, StringBuffer sb) {
      if (statistics.containsToolQuestionStatistics(question)) {
         sb.append("<tr>");
         sb.append("<td><b>");
         sb.append(question.getName());
         sb.append("</b></td>");
         for (IStatisticsFilter filter : statistics.getFilters()) {
            FilteredStatistics fs = statistics.getFilteredStatistics(filter);
            Set<Tool> winningCorrectTools = fs.computeWinningCorrectTools(question);
            Set<Tool> winningCorrectTrustTools = fs.computeWinningCorrectTrustTools(question);
            Set<Tool> winningTimesTools = fs.computeWinningTimeTools(question);
            Set<Tool> winningTrustTimesTools = fs.computeWinningTrustTimeTools(question);
            Set<Tool> winningTrustScoreTools = fs.computeWinningTrustScoreTools(question);
            for (Tool tool : evaluation.getTools()) {
               QuestionStatistics toolQs = fs.getQuestionStatistics(tool, question);
               appendQuestionValues(toolQs, winningCorrectTools, winningCorrectTrustTools, winningTimesTools, winningTrustTimesTools, winningTrustScoreTools, tool, false, sb);
            }
         }
         sb.append("</tr>");
      }
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (choiceQuestion.hasChildQuestions()) {
            for (Choice choice : choiceQuestion.getChoices()) {
               if (choice.countChildQuestions() > 0) {
                  for (AbstractQuestion cildQuestion : choice.getChildQuestions()) {
                     appendQuestion(evaluation, statistics, cildQuestion, sb);
                  }
               }
            }
         }
      }
      else if (question instanceof IQuestionWithCildren) {
         IQuestionWithCildren withChildrenQuestion = (IQuestionWithCildren) question;
         if (withChildrenQuestion.countChildQuestions() > 0) {
            for (AbstractQuestion cildQuestion : withChildrenQuestion.getChildQuestions()) {
               appendQuestion(evaluation, statistics, cildQuestion, sb);
            }
         }
      }
   }
   
   /**
    * Appends the values.
    * @param qs The {@link QuestionStatistics} to append.
    * @param winningCorrectTools The winning {@link Tool}s.
    * @param winningCorrectTrustTools The winning {@link Tool}s.
    * @param winningTimesTools The winning {@link Tool}s.
    * @param winningTrustTimesTools The winning {@link Tool}s.
    * @param winningTrustScoreTools The winning {@link Tool}s.
    * @param currentTool The current {@link Tool}.
    * @param bold {@code true} values are bold, {@code false} values are normla,
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendQuestionValues(QuestionStatistics qs, 
                                       Set<Tool> winningCorrectTools, 
                                       Set<Tool> winningCorrectTrustTools, 
                                       Set<Tool> winningTimesTools, 
                                       Set<Tool> winningTrustTimesTools,
                                       Set<Tool> winningTrustScoreTools,
                                       Tool currentTool, 
                                       boolean bold,
                                       StringBuffer sb) {
      if (qs != null) {
         appendQuestionValues(qs.computeCorrect(), 
                              qs.computeWrong(), 
                              qs.computeAverageCorrectnessScore(),
                              qs.computeAverageTime(), 
                              qs.computeTrustCorrect(),
                              qs.computeTrustWrong(),
                              qs.computeAverageTrustScore(),
                              qs.computeAverageTrustTime(),
                              winningCorrectTools, 
                              winningCorrectTrustTools, 
                              winningTimesTools, 
                              winningTrustTimesTools, 
                              winningTrustScoreTools,
                              currentTool, 
                              bold,
                              sb);
      }
      else {
         sb.append("<td colspan=\"8\">&nbsp;</td>");
      }
   }
   
   /**
    * Appends the values.
    * @param correct The computed value to append.
    * @param wrong The computed value to append.
    * @param averageCorrectnessScore The average correctness score.
    * @param averageTime The computed value to append.
    * @param trustCorrect The computed value to append.
    * @param trustWrong The computed value to append.
    * @param averageTrustScore The computed value to append.
    * @param averageTrustTime The computed value to append.
    * @param winningCorrectTools The winning {@link Tool}s.
    * @param winningCorrectTrustTools The winning {@link Tool}s.
    * @param winningTimesTools The winning {@link Tool}s.
    * @param winningTrustTimesTools The winning {@link Tool}s.
    * @param winningTrustScoreTools The winning {@link Tool}s.
    * @param currentTool The current {@link Tool}.
    * @param bold {@code true} values are bold, {@code false} values are normal,
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendQuestionValues(BigDecimal correct,
                                       BigDecimal wrong,
                                       BigDecimal averageCorrectnessScore,
                                       BigInteger averageTime,
                                       BigDecimal trustCorrect,
                                       BigDecimal trustWrong,
                                       BigDecimal averageTrustScore,
                                       BigInteger averageTrustTime,
                                       Set<Tool> winningCorrectTools, 
                                       Set<Tool> winningCorrectTrustTools, 
                                       Set<Tool> winningTimesTools, 
                                       Set<Tool> winningTrustTimesTools,
                                       Set<Tool> winningTrustScoreTools,
                                       Tool currentTool, 
                                       boolean bold,
                                       StringBuffer sb) {
      if (winningCorrectTools != null && winningCorrectTools.contains(currentTool)) {
         String color = winningCorrectTools.size() == 1 ?
                        "blue" :
                        "#FF00FF";
         appendQuestionValue(bold, color, correct + "&nbsp;%", sb);
         appendQuestionValue(bold, color, wrong + "&nbsp;%", sb);
         appendQuestionValue(bold, color, averageCorrectnessScore, sb);
      }
      else {
         appendQuestionValue(bold, null, correct + "&nbsp;%", sb);
         appendQuestionValue(bold, null, wrong + "&nbsp;%", sb);
         appendQuestionValue(bold, null, averageCorrectnessScore, sb);
      }
      if (winningTimesTools != null && winningTimesTools.contains(currentTool)) {
         String color = winningTimesTools.size() == 1 ?
                        "blue" :
                        "#FF00FF";
         appendQuestionValue(bold, color, averageTime + "&nbsp;ms", sb);
      }
      else {
         appendQuestionValue(bold, null, averageTime + "&nbsp;ms", sb);
      }
      if (winningCorrectTrustTools != null && winningCorrectTrustTools.contains(currentTool)) {
         String color = winningCorrectTrustTools.size() == 1 ?
                        "blue" :
                        "#FF00FF";
         appendQuestionValue(bold, color, trustCorrect + "&nbsp;%", sb);
         appendQuestionValue(bold, color, trustWrong + "&nbsp;%", sb);
      }
      else {
         appendQuestionValue(bold, null, trustCorrect + "&nbsp;%", sb);
         appendQuestionValue(bold, null, trustWrong + "&nbsp;%", sb);
      }
      if (winningTrustScoreTools != null && winningTrustScoreTools.contains(currentTool)) {
         String color = winningTrustScoreTools.size() == 1 ?
                        "blue" :
                        "#FF00FF";
         appendQuestionValue(bold, color, averageTrustScore, sb);
      }
      else {
         appendQuestionValue(bold, null, averageTrustScore, sb);
      }
      if (winningTrustTimesTools != null && winningTrustTimesTools.contains(currentTool)) {
         String color = winningTrustTimesTools.size() == 1 ?
                        "blue" :
                        "#FF00FF";
         appendQuestionValue(bold, color, averageTrustTime + "&nbsp;ms", sb);
      }
      else {
         appendQuestionValue(bold, null, averageTrustTime + "&nbsp;ms", sb);
      }
   }
   
   /**
    * Appends the single table cell value.
    * @param bold Show value in bold?
    * @param fontColor The optional font color.
    * @param value The value to show.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendQuestionValue(boolean bold, String fontColor, Object value, StringBuffer sb) {
      sb.append("<td align=\"right\">");
      if (bold) {
         sb.append("<b>");
      }
      if (fontColor != null) {
         sb.append("<font color=\"" + fontColor + "\">");
      }
      sb.append(value);
      if (fontColor != null) {
         sb.append("</font>");
      }
      if (bold) {
         sb.append("</b>");
      }
      sb.append("</td>");
   }
   
   /**
    * Counts the {@link QuestionStatistics}.
    * @param statistics The {@link Statistics} to count in.
    * @param form The {@link AbstractForm} to count.
    * @return The results.
    */
   protected Map<AbstractPage, Integer> countStatistics(Statistics statistics, AbstractForm form) {
      Map<AbstractPage, Integer> result = new HashMap<AbstractPage, Integer>();
      for (AbstractPage page : form.getPages()) {
         int pageCount = 0;
         if (statistics.containsToolPageStatistics(page)) {
            if (page instanceof QuestionPage) {
               QuestionPage questionPage = (QuestionPage) page;
               for (AbstractQuestion question : questionPage.getQuestions()) {
                  pageCount += countStatistics(statistics, question);
               }
            }
            else {
               throw new IllegalStateException("Unsupported page: " + page);
            }
         }
         result.put(page, pageCount);
      }
      return result;
   }
   
   /**
    * Counts the {@link QuestionStatistics}.
    * @param statistics The {@link Statistics} to count in.
    * @param question The current {@link AbstractQuestion}.
    * @return The number of entries.
    */
   protected int countStatistics(Statistics statistics, AbstractQuestion question) {
      int questionCount = 0;
      if (statistics.containsToolQuestionStatistics(question)) {
         questionCount++;
      }
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (choiceQuestion.hasChildQuestions()) {
            for (Choice choice : choiceQuestion.getChoices()) {
               if (choice.countChildQuestions() > 0) {
                  for (AbstractQuestion childQuestion : choice.getChildQuestions()) {
                     questionCount += countStatistics(statistics, childQuestion);
                  }
               }
            }
         }
      }
      else if (question instanceof IQuestionWithCildren) {
         IQuestionWithCildren withChildrenQuestion = (IQuestionWithCildren) question;
         if (withChildrenQuestion.countChildQuestions() > 0) {
            for (AbstractQuestion childQuestion : withChildrenQuestion.getChildQuestions()) {
               questionCount += countStatistics(statistics, childQuestion);
            }
         }
      }
      return questionCount;
   }
}
