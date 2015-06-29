package org.key_project.sed.key.evaluation.server.report;

import java.io.File;
import java.math.BigInteger;
import java.text.DateFormat;
import java.util.Date;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.sed.key.evaluation.model.definition.SectionQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.EvaluationInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.FilteredStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.PageStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.QuestionStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.StringUtil;

/**
 * A report engine which generates HTML reports.
 * @author Martin Hentschel
 */
public class HTMLReportEngine extends AbstractReportEngine {
   /**
    * Constructor.
    * @param storageLocation The file storage.
    */
   public HTMLReportEngine(File storageLocation) {
      super(storageLocation);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String createReport(AbstractEvaluation evaluation) throws Exception {
      // List reports
      Map<AbstractForm, List<EvaluationInput>> formInputs = listForms(evaluation);
      // Analyze reports
      EvaluationResult result = analyzeReports(formInputs);
      if (!formInputs.isEmpty()) {
         // Create HTML report
         StringBuffer sb = new StringBuffer();
         sb.append("<html>");
         sb.append("<head>");
         sb.append("<title>");
         sb.append(evaluation.getName());
         sb.append("</title>");
         sb.append("</head>");
         sb.append("<body>");
         appendToolStatistics(evaluation, result, sb);
         appendReceivedAnswers(evaluation, result, sb);
         sb.append("</body>");
         sb.append("</html>");
         return sb.toString();
      }
      else {
         return null;
      }
   }

   /**
    * Appends the computed statistics to the HTML report.
    * @param evaluation The analyzed {@link AbstractEvaluation}.
    * @param result The found {@link EvaluationResult}s.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendToolStatistics(AbstractEvaluation evaluation, EvaluationResult result, StringBuffer sb) {
      Statistics statistics = computeStatistics(evaluation, result);
      sb.append("<h1><a name=\"statistics\">Tool Comparison</a></h1>");
      sb.append("<table border=\"1\">");
      // Append header
      sb.append("<tr>");
      sb.append("<td rowspan=\"3\" colspan=\"3\">&nbsp;</td>");
      for (IStatisticsFilter filter : statistics.getFilters()) {
         sb.append("<td colspan=\"" + ((evaluation.getTools().length) * 6) + "\" align=\"center\"><b>");
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
            sb.append("<td colspan=\"6\" align=\"center\"><b>");
            sb.append(tool.getName());
            sb.append("</b></td>");
         }
      }
      sb.append("</tr>");
      sb.append("<tr>");
      for (@SuppressWarnings("unused") IStatisticsFilter filter : statistics.getFilters()) {
         for (@SuppressWarnings("unused") Tool tool : evaluation.getTools()) {
            appendToolStatisticsQuestionHeaders(sb);
         }
      }
      sb.append("</tr>");
      // Append content
      for (AbstractForm form : evaluation.getForms()) {
         Map<AbstractPage, Integer> questionCount = countQuestionStatistics(statistics, form);
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
            sb.append("<td colspan=\"" + (2 + ((evaluation.getTools().length) * 6 * statistics.getFilters().size())) + "\">&nbsp;</td>");
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
                        sb.append("<td colspan=\"2\">&nbsp;</td>");
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
                        sb.append("<td colspan=\"3\">&nbsp;</td>");
                     }
                  }
                  sb.append("</tr>");
                  if (page instanceof QuestionPage) {
                     QuestionPage questionPage = (QuestionPage) page;
                     for (AbstractQuestion question : questionPage.getQuestions()) {
                        appendToolStatisticsQuestion(evaluation, statistics, question, sb);
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
                  appendToolStatisticsQuestionValues(questionStatistics.get(tool), 
                                                     FilteredStatistics.computeWinningCorrectTools(questionStatistics), 
                                                     FilteredStatistics.computeWinningCorrectTrustTools(questionStatistics), 
                                                     FilteredStatistics.computeWinningTimeTools(questionStatistics), 
                                                     FilteredStatistics.computeWinningTrustTimeTools(questionStatistics), 
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
   }
   
   /**
    * Appends the tool static question headers.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendToolStatisticsQuestionHeaders(StringBuffer sb) {
      sb.append("<td align=\"center\"><b>Correct</b></td>");
      sb.append("<td align=\"center\"><b>Wrong</b></td>");
      sb.append("<td align=\"center\"><b>Average Time</b></td>");
      sb.append("<td align=\"center\"><b>Trust Correct</b></td>");
      sb.append("<td align=\"center\"><b>Trust Wrong</b></td>");
      sb.append("<td align=\"center\"><b>Average Trust Time</b></td>");
   }

   /**
    * Appends the tool statistics of the given {@link AbstractQuestion}.
    * @param evaluation The analyzed {@link AbstractEvaluation}.
    * @param statistics The computed {@link Statistics}.
    * @param question The {@link AbstractQuestion} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendToolStatisticsQuestion(AbstractEvaluation evaluation, Statistics statistics, AbstractQuestion question, StringBuffer sb) {
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
            for (Tool tool : evaluation.getTools()) {
               QuestionStatistics toolQs = fs.getQuestionStatistics(tool, question);
               appendToolStatisticsQuestionValues(toolQs, winningCorrectTools, winningCorrectTrustTools, winningTimesTools, winningTrustTimesTools, tool, false, sb);
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
                     appendToolStatisticsQuestion(evaluation, statistics, cildQuestion, sb);
                  }
               }
            }
         }
      }
      else if (question instanceof SectionQuestion) {
         SectionQuestion sectionQuestion = (SectionQuestion) question;
         if (sectionQuestion.countChildQuestions() > 0) {
            for (AbstractQuestion cildQuestion : sectionQuestion.getChildQuestions()) {
               appendToolStatisticsQuestion(evaluation, statistics, cildQuestion, sb);
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
    * @param currentTool The current {@link Tool}.
    * @param bold {@code true} values are bold, {@code false} values are normla,
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendToolStatisticsQuestionValues(QuestionStatistics qs, 
                                                     Set<Tool> winningCorrectTools, 
                                                     Set<Tool> winningCorrectTrustTools, 
                                                     Set<Tool> winningTimesTools, 
                                                     Set<Tool> winningTrustTimesTools,
                                                     Tool currentTool, 
                                                     boolean bold,
                                                     StringBuffer sb) {
      if (qs != null) {
         appendToolStatisticsQuestionValues(qs.computeCorrect(), 
                                            qs.computeWrong(), 
                                            qs.computeAverageTime(), 
                                            qs.computeTrustCorrect(),
                                            qs.computeTrustWrong(),
                                            qs.computeAverageTrustTime(),
                                            winningCorrectTools, 
                                            winningCorrectTrustTools, 
                                            winningTimesTools, 
                                            winningTrustTimesTools, 
                                            currentTool, 
                                            bold,
                                            sb);
      }
      else {
         sb.append("<td colspan=\"6\">&nbsp;</td>");
      }
   }
   
   /**
    * Appends the values.
    * @param correct The computed value to append.
    * @param wrong The computed value to append.
    * @param averageTime The computed value to append.
    * @param trustCorrect The computed value to append.
    * @param trustWrong The computed value to append.
    * @param averageTrustTime The computed value to append.
    * @param winningCorrectTools The winning {@link Tool}s.
    * @param winningCorrectTrustTools The winning {@link Tool}s.
    * @param winningTimesTools The winning {@link Tool}s.
    * @param winningTrustTimesTools The winning {@link Tool}s.
    * @param currentTool The current {@link Tool}.
    * @param bold {@code true} values are bold, {@code false} values are normla,
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendToolStatisticsQuestionValues(BigInteger correct,
                                                     BigInteger wrong,
                                                     BigInteger averageTime,
                                                     BigInteger trustCorrect,
                                                     BigInteger trustWrong,
                                                     BigInteger averageTrustTime,
                                                     Set<Tool> winningCorrectTools, 
                                                     Set<Tool> winningCorrectTrustTools, 
                                                     Set<Tool> winningTimesTools, 
                                                     Set<Tool> winningTrustTimesTools,
                                                     Tool currentTool, 
                                                     boolean bold,
                                                     StringBuffer sb) {
      if (winningCorrectTools != null && winningCorrectTools.contains(currentTool)) {
         String color = winningCorrectTools.size() == 1 ?
                        "blue" :
                        "#FF00FF";
         appendToolStatisticsQuestionValue(bold, color, correct + "&nbsp;%", sb);
         appendToolStatisticsQuestionValue(bold, color, wrong + "&nbsp;%", sb);
      }
      else {
         appendToolStatisticsQuestionValue(bold, null, correct + "&nbsp;%", sb);
         appendToolStatisticsQuestionValue(bold, null, wrong + "&nbsp;%", sb);
      }
      if (winningTimesTools != null && winningTimesTools.contains(currentTool)) {
         String color = winningTimesTools.size() == 1 ?
                        "blue" :
                        "#FF00FF";
         appendToolStatisticsQuestionValue(bold, color, averageTime + "&nbsp;ms", sb);
      }
      else {
         appendToolStatisticsQuestionValue(bold, null, averageTime + "&nbsp;ms", sb);
      }
      if (winningCorrectTrustTools != null && winningCorrectTrustTools.contains(currentTool)) {
         String color = winningCorrectTrustTools.size() == 1 ?
                        "blue" :
                        "#FF00FF";
         appendToolStatisticsQuestionValue(bold, color, trustCorrect + "&nbsp;%", sb);
         appendToolStatisticsQuestionValue(bold, color, trustWrong + "&nbsp;%", sb);
      }
      else {
         appendToolStatisticsQuestionValue(bold, null, trustCorrect + "&nbsp;%", sb);
         appendToolStatisticsQuestionValue(bold, null, trustWrong + "&nbsp;%", sb);
      }
      if (winningTrustTimesTools != null && winningTrustTimesTools.contains(currentTool)) {
         String color = winningTrustTimesTools.size() == 1 ?
                        "blue" :
                        "#FF00FF";
         appendToolStatisticsQuestionValue(bold, color, averageTrustTime + "&nbsp;ms", sb);
      }
      else {
         appendToolStatisticsQuestionValue(bold, null, averageTrustTime + "&nbsp;ms", sb);
      }
   }
   
   protected void appendToolStatisticsQuestionValue(boolean bold, String fontColor, Object value, StringBuffer sb) {
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
   protected Map<AbstractPage, Integer> countQuestionStatistics(Statistics statistics, AbstractForm form) {
      Map<AbstractPage, Integer> result = new HashMap<AbstractPage, Integer>();
      for (AbstractPage page : form.getPages()) {
         int pageCount = 0;
         if (statistics.containsToolPageStatistics(page)) {
            if (page instanceof QuestionPage) {
               QuestionPage questionPage = (QuestionPage) page;
               for (AbstractQuestion question : questionPage.getQuestions()) {
                  pageCount += countQuestionStatistics(statistics, question);
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
   protected int countQuestionStatistics(Statistics statistics, AbstractQuestion question) {
      int questionCount = 0;
      if (statistics.containsToolQuestionStatistics(question)) {
         questionCount++;
      }
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (choiceQuestion.hasChildQuestions()) {
            for (Choice choice : choiceQuestion.getChoices()) {
               if (choice.countChildQuestions() > 0) {
                  for (AbstractQuestion cildQuestion : choice.getChildQuestions()) {
                     questionCount += countQuestionStatistics(statistics, cildQuestion);
                  }
               }
            }
         }
      }
      else if (question instanceof SectionQuestion) {
         SectionQuestion sectionQuestion = (SectionQuestion) question;
         if (sectionQuestion.countChildQuestions() > 0) {
            for (AbstractQuestion cildQuestion : sectionQuestion.getChildQuestions()) {
               questionCount += countQuestionStatistics(statistics, cildQuestion);
            }
         }
      }
      return questionCount;
   }

   /**
    * Appends the received answers to the HTML report.
    * @param evaluation The analyzed {@link AbstractEvaluation}.
    * @param result The found {@link EvaluationResult}s.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendReceivedAnswers(AbstractEvaluation evaluation, 
                                        EvaluationResult result, 
                                        StringBuffer sb) {
      // Append table header
      sb.append("<h1><a name=\"answers\">Received Answers</a></h1>");
      sb.append("<table border=\"1\">");
      // Append header
      List<Object> questionOrder = new LinkedList<Object>();
      appendReceivedAnswersResultsHeader(evaluation, sb, questionOrder);
      // Append answers
      for (Entry<String, EvaluationAnswers> entry : result.getIdInputMap().entrySet()) {
         if (entry.getValue().hasMultipleValues()) {
            sb.append("<tr bgcolor=\"#C3C3C3\">");
         }
         else {
            sb.append("<tr>");
         }
         sb.append("<td>");
         sb.append(entry.getKey()); // UUID
         sb.append("</td>");
         for (Object object : questionOrder) {
            if (object instanceof AbstractQuestion) {
               List<QuestionInput> answers = entry.getValue().getQuestionInputs((AbstractQuestion) object);
               if (!CollectionUtil.isEmpty(answers)) {
                  sb.append("<td>");
                  boolean afterFirst = false;
                  for (QuestionInput questionInput : answers) {
                     if (afterFirst) {
                        sb.append("<br>");
                     }
                     else {
                        afterFirst = true;
                     }
                     if (!StringUtil.isTrimmedEmpty(questionInput.getValue())) {
                        Boolean correct = questionInput.checkCorrectness();
                        appendReceivedAnswersTableCellValue(questionInput.getValue(), correct, questionInput.getValueSetAt(), sb);
                        if (questionInput.getQuestion().isAskForTrust()) {
                           sb.append(" (");
                           Boolean trust = questionInput.getTrust();
                           if (trust != null) {
                              if (trust) {
                                 appendReceivedAnswersTableCellValue("trusted", questionInput.checkTrust(), questionInput.getTrustSetAt(), sb);
                              }
                              else {
                                 appendReceivedAnswersTableCellValue("untrusted", questionInput.checkTrust(), questionInput.getTrustSetAt(), sb);
                              }
                           }
                           else {
                              appendReceivedAnswersTableCellValue("trust&nbsp;missing", questionInput.checkTrust(), questionInput.getTrustSetAt(), sb);
                           }
                           sb.append(")");
                        }
                     }
                     else {
                        sb.append("&nbsp;");
                     }
                  }
                  sb.append("</td>");
               }
               else {
                  sb.append("<td>&nbsp;</td>");
               }
            }
            else if (object instanceof AbstractPage) {
               AbstractPage page = (AbstractPage) object;
               if (page.getForm().isCollectTimes()) {
                  List<AbstractPageInput<?>> pages = entry.getValue().getPageInputs(page);
                  if (!CollectionUtil.isEmpty(pages)) {
                     sb.append("<td>");
                     boolean afterFirst = false;
                     for (AbstractPageInput<?> pageInput : pages) {
                        if (afterFirst) {
                           sb.append("<br>");
                        }
                        else {
                           afterFirst = true;
                        }
                        sb.append(pageInput.getShownTime());
                     }
                     sb.append("</td>");
                  }
                  else {
                     sb.append("<td>&nbsp;</td>");
                  }
               }
               if (page.isToolBased()) {
                  List<Tool> tools = entry.getValue().getTools(page);
                  if (!CollectionUtil.isEmpty(tools)) {
                     sb.append("<td>");
                     boolean afterFirst = false;
                     for (Tool tool : tools) {
                        if (afterFirst) {
                           sb.append("<br>");
                        }
                        else {
                           afterFirst = true;
                        }
                        sb.append(tool != null ? tool.getName() : "&nbsp;");
                     }
                     sb.append("</td>");
                  }
                  else {
                     sb.append("<td>&nbsp;</td>");
                  }
               }
            }
            else if (object instanceof AbstractForm) {
               AbstractForm form = (AbstractForm) object;
               List<AbstractFormInput<?>> forms = entry.getValue().getFormInputs(form);
               if (!CollectionUtil.isEmpty(forms)) {
                  sb.append("<td>");
                  boolean afterFirst = false;
                  for (AbstractFormInput<?> formInput : forms) {
                     if (afterFirst) {
                        sb.append("<br>");
                     }
                     else {
                        afterFirst = true;
                     }
                     sb.append(DateFormat.getDateTimeInstance().format(new Date(formInput.getEvaluationInput().getTimestamp())));
                  }
                  sb.append("</td>");
               }
               else {
                  sb.append("<td>&nbsp;</td>");
               }
            }
         }
         sb.append("</tr>");
      }
      // Append table footer
      sb.append("</table>");
   }
   
   /**
    * Appends a cell value to the given {@link StringBuffer}.
    * @param value The value to append.
    * @param correct The optional correctness.
    * @param time The optional time.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected void appendReceivedAnswersTableCellValue(String value, Boolean correct, long time, StringBuffer sb) {
      if (correct != null) {
         if (correct) {
            sb.append("<font color=\"green\">");
         }
         else {
            sb.append("<font color=\"red\">");
         }
      }
      if (value != null) {
         sb.append(value);
      }
      else {
         sb.append("&nbsp;");
      }
      if (time > 0) {
         sb.append(" [");
         sb.append(time);
         sb.append(" ]");
      }
      if (correct != null) {
         sb.append("</font>");
      }
   }
   
   /**
    * Appends the table header rows.
    * @param evaluation The {@link AbstractEvaluation}.
    * @param sb The {@link StringBuffer} to append to.
    * @param questionOrder The {@link List} with the order of the {@link AbstractQuestion} to fill.
    */
   protected void appendReceivedAnswersResultsHeader(AbstractEvaluation evaluation, StringBuffer sb, List<Object> questionOrder) {
      // Create question header
      Map<Object, Integer> spanMap = new HashMap<Object, Integer>();
      StringBuffer questionHeader = createReceivedAnswersQuestionHeader(evaluation, spanMap, questionOrder);
      sb.append("<tr>");
      sb.append("<td>&nbsp;</td>"); // UUID
      for (AbstractForm form : evaluation.getForms()) {
         int colspan = spanMap.get(form);
         if (colspan > 0) {
            sb.append("<td colspan=\"" + colspan + "\"><b>");
            sb.append(form.getName());
            sb.append("</b></td>");
         }
      }
      sb.append("</tr>");
      sb.append("<tr>");
      sb.append("<td>&nbsp;</td>"); // UUID
      for (AbstractForm form : evaluation.getForms()) {
         for (AbstractPage page : form.getPages()) {
            int colspan = spanMap.get(page);
            if (colspan > 0) {
               sb.append("<td colspan=\"" + colspan + "\"><b>");
               sb.append(page.getName());
               sb.append("</b></td>");
            }
         }
         sb.append("<td>&nbsp;</td>"); // Date
      }
      sb.append("</tr>");
      sb.append("<tr>");
      sb.append(questionHeader);
      sb.append("</tr>");
   }

   /**
    * Creates the question header row.
    * @param evaluation The {@link AbstractEvaluation}.
    * @param spanMap The span {@link Map} to fill.
    * @param questionOrder The {@link List} with the order of the {@link AbstractQuestion} to fill.
    * @return The computed question header row.
    */
   protected StringBuffer createReceivedAnswersQuestionHeader(AbstractEvaluation evaluation, Map<Object, Integer> spanMap, List<Object> questionOrder) {
      StringBuffer sb = new StringBuffer();
      sb.append("<td><b>UUID</b></td>");
      for (AbstractForm form : evaluation.getForms()) {
         int formSpan = 0;
         for (AbstractPage page : form.getPages()) {
            int pageSpan = 0;
            if (!page.isReadonly()) {
               if (page instanceof QuestionPage) {
                  QuestionPage questionPage = (QuestionPage) page;
                  for (AbstractQuestion question : questionPage.getQuestions()) {
                     pageSpan += appendReceivedAnswersQuestionHeader(question, sb, questionOrder);
                  }
               }
               else {
                  throw new IllegalStateException("Unsupported page: " + page);
               }
               boolean addPageToOrder = false;
               if (form.isCollectTimes()) {
                  sb.append("<td><b>Shown Time</b></td>");
                  addPageToOrder = true;
                  pageSpan++;
               }
               if (form instanceof RandomForm) {
                  if (page.isToolBased()) {
                     sb.append("<td><b>Tool</b></td>");
                     addPageToOrder = true;
                     pageSpan++;
                  }
               }
               if (addPageToOrder) {
                  questionOrder.add(page);
               }
            }
            formSpan += pageSpan;
            spanMap.put(page, pageSpan);
         }
         sb.append("<td><b>Date</b></td>");
         questionOrder.add(form);
         formSpan++;
         spanMap.put(form, formSpan);
      }
      return sb;
   }
   
   /**
    * Appends the given {@link AbstractQuestion} and its children as header to the {@link StringBuffer}.
    * @param question The {@link AbstractQuestion} to append.
    * @param sb The {@link StringBuffer} to append to.
    * @param questionOrder The {@link List} with the order of the {@link AbstractQuestion} to fill.
    * @return The number of appended questions.
    */
   protected int appendReceivedAnswersQuestionHeader(AbstractQuestion question, StringBuffer sb, List<Object> questionOrder) {
      int questionCount = 0;
      if (question.isEditable()) {
         questionOrder.add(question);
         sb.append("<td><b>");
         sb.append(question.getName());
         sb.append("</b></td>");
         questionCount++;
      }
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (choiceQuestion.hasChildQuestions()) {
            for (Choice choice : choiceQuestion.getChoices()) {
               if (choice.countChildQuestions() > 0) {
                  for (AbstractQuestion cildQuestion : choice.getChildQuestions()) {
                     questionCount += appendReceivedAnswersQuestionHeader(cildQuestion, sb, questionOrder);
                  }
               }
            }
         }
      }
      else if (question instanceof SectionQuestion) {
         SectionQuestion sectionQuestion = (SectionQuestion) question;
         if (sectionQuestion.countChildQuestions() > 0) {
            for (AbstractQuestion cildQuestion : sectionQuestion.getChildQuestions()) {
               questionCount += appendReceivedAnswersQuestionHeader(cildQuestion, sb, questionOrder);
            }
         }
      }
      return questionCount;
   }   
}
