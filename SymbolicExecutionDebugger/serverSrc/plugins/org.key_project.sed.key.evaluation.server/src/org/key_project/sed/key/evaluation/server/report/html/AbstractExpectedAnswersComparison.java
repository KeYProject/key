package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.IQuestionWithCildren;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.StringUtil;

/**
 * Provides the basic functionality to export the knowledge of the participants as LaTeX file.
 * @author Martin Hentschel
 */
public abstract class AbstractExpectedAnswersComparison implements IHTMLSectionAppender {
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, 
                                                   AbstractEvaluation evaluation, 
                                                   EvaluationResult result, 
                                                   Statistics statistics, 
                                                   StringBuffer sb) {
      // Compute statistic
      Map<IStatisticsFilter, BigInteger> recordsCount = new HashMap<IStatisticsFilter, BigInteger>();
      for (IStatisticsFilter filter : statistics.getFilters()) {
         recordsCount.put(filter, BigInteger.ZERO);
      }
      Map<AbstractPage, PageStatistic> pageMap = new LinkedHashMap<AbstractPage, PageStatistic>();
      for (Entry<String, EvaluationAnswers> entry : result.getIdInputMap().entrySet()) {
         boolean recordsCountUpdated = false;
         if (!entry.getValue().hasMultipleValues()) {
            for (AbstractForm form : entry.getValue().getForms()) {
               for (AbstractPage page : form.getPages()) {
                  List<AbstractQuestion> questionsWithResults = listQuestionsWithResults(page);
                  if (!questionsWithResults.isEmpty()) {
                     if (!recordsCountUpdated) {
                        for (IStatisticsFilter filter : statistics.getFilters()) {
                           if (filter.accept(entry.getValue())) {
                              recordsCount.put(filter, recordsCount.get(filter).add(BigInteger.ONE));
                           }
                        }
                        recordsCountUpdated = true;
                     }
                     PageStatistic ps = pageMap.get(page);
                     if (ps == null) {
                        ps = new PageStatistic(page);
                        pageMap.put(page, ps);
                     }
                     List<Tool> tools = entry.getValue().getTools(page);
                     if (!CollectionUtil.isEmpty(tools)) { // It might be empty in the reviewing code evaluation when the extend is four examples.
                        Tool tool = tools.get(0);
                        for (AbstractQuestion question : questionsWithResults) {
                           QuestionStatistic qs = ps.getQuestionStatistic(question);
                           QuestionInput qi = entry.getValue().getQuestionInputs(question).get(0);
                           for (Choice choice : ((AbstractChoicesQuestion) question).getCorrectChoices()) {
                              boolean selected = qi.isChoiceSelected(choice);
                              ChoiceStatistic cs = qs.getChoiceStatistic(choice);
                              for (IStatisticsFilter filter : statistics.getFilters()) {
                                 if (filter.accept(entry.getValue())) {
                                    Statistic statistic = cs.getStatistic(filter, tool);
                                    statistic.update(selected);
                                 }
                              }
                           }
                        }
                     }
                  }
               }
            }
         }
      }
      // Append statistic
      sb.append("<h1><a name=\"expectedAnswers\">Expected Answers Comparison</a></h1>");
      sb.append("<table border=\"1\">");
      // Append header
      sb.append("<tr>");
      sb.append("<td rowspan=\"2\" colspan=\"3\">&nbsp;</td>");
      for (IStatisticsFilter filter : statistics.getFilters()) {
         sb.append("<td colspan=\"" + evaluation.getTools().length + "\" align=\"center\"><b>");
         sb.append(filter.getName());
         sb.append(" (");
         sb.append(recordsCount.get(filter));
         sb.append(" answers)");
         sb.append("</b></td>");
      }
      sb.append("</tr>");
      sb.append("<tr>");
      for (@SuppressWarnings("unused") IStatisticsFilter filter : statistics.getFilters()) {
         for (Tool tool : evaluation.getTools()) {
            sb.append("<td align=\"center\"><b>");
            sb.append(tool.getName());
            sb.append("</b></td>");
         }
      }
      sb.append("</tr>");
      Map<IStatisticsFilter, Map<Tool, BigInteger>> winningMap = new HashMap<IStatisticsFilter, Map<Tool, BigInteger>>();
      for (PageStatistic ps : pageMap.values()) {
         Collection<QuestionStatistic> qss = ps.getQuestionStatistics();
         boolean pagePrinted = false;
         for (QuestionStatistic qs : qss) {
            boolean questionPrinted = false;
            Collection<ChoiceStatistic> css = qs.getChoiceStatistics();
            for (ChoiceStatistic cs : css) {
               sb.append("<tr>");
               if (!pagePrinted) {
                  int choicesCount = 0;
                  for (QuestionStatistic currentQs : qss) {
                     choicesCount += currentQs.getChoiceStatistics().size();
                  }
                  sb.append("<td rowspan=\"" + choicesCount + "\" valign=\"top\">" + ps.getPage().getTitle() + "</td>");
                  pagePrinted = true;
               }
               if (!questionPrinted) {
                  sb.append("<td rowspan=\"" + css.size() + "\" valign=\"top\">" + qs.getQuestion().getLabel() + "</td>");
                  questionPrinted = true;
               }
               sb.append("<td>" + cs.getChoice().getText() + "</td>");
               for (IStatisticsFilter filter : statistics.getFilters()) {
                  List<Tool> winningTools = cs.computeWinningTools(filter, evaluation.getTools());
                  if (winningTools != null && winningTools.size() == 1) {
                     Map<Tool, BigInteger> filterMap = winningMap.get(filter);
                     if (filterMap == null) {
                        filterMap = new HashMap<Tool, BigInteger>();
                        winningMap.put(filter, filterMap);
                     }
                     BigInteger currentValue = filterMap.get(winningTools.get(0));
                     if (currentValue == null) {
                        currentValue = BigInteger.ONE;
                     }
                     else {
                        currentValue = currentValue.add(BigInteger.ONE);
                     }
                     filterMap.put(winningTools.get(0), currentValue);
                  }
                  for (Tool tool : evaluation.getTools()) {
                     Statistic s = cs.getStatistic(filter, tool);
                     BigDecimal percentage = s.computePercentage();
                     if (winningTools != null && winningTools.contains(tool)) {
                        String color = winningTools.size() == 1 ?
                                       "blue" :
                                       "#FF00FF";
                        sb.append("<td align=\"right\"><font color=\"" + color + "\">" + (percentage != null ? percentage : "&nbsp;") + "</font></td>");
                     }
                     else {
                        sb.append("<td align=\"right\">" + (percentage != null ? percentage : "&nbsp;") + "</td>");
                     }
                  }
               }
               sb.append("</tr>");
            }
         }
      }
      sb.append("<tr>");
      sb.append("<td colspan=\"3\">&nbsp;</td>");
      for (IStatisticsFilter filter : statistics.getFilters()) {
         Map<Tool, BigInteger> filterMap = winningMap.get(filter);
         List<Tool> winningTools = new LinkedList<Tool>();
         if (filterMap != null) {
            BigInteger winningCount = null;
            for (Tool tool : evaluation.getTools()) {
               BigInteger current = filterMap.get(tool);
               if (current == null) {
                  current = BigInteger.ZERO;
               }
               if (winningCount == null) {
                  winningTools.add(tool);
                  winningCount = current;
               }
               else {
                  if (winningCount.compareTo(current) == 0) {
                     winningTools.add(tool);
                  }
                  else if (winningCount.compareTo(current) < 0) {
                     winningTools.clear();
                     winningTools.add(tool);
                     winningCount = current;
                  }
               }
            }
         }
         for (Tool tool : evaluation.getTools()) {
            BigInteger value = filterMap != null ? filterMap.get(tool) : null;
            if (winningTools.contains(tool)) {
               String color = winningTools.size() == 1 ?
                              "blue" :
                              "#FF00FF";
               sb.append("<td align=\"right\"><b><font color=\"" + color + "\">" + (value != null ? value : BigInteger.ZERO) + "</font></b></td>");
            }
            else {
               sb.append("<td align=\"right\"><b>" + (value != null ? value : BigInteger.ZERO) + "</b></td>");
            }
         }
      }
      sb.append("</tr>");
      sb.append("</table>");
      return CollectionUtil.toList(createLatexFile(evaluation, statistics, recordsCount, pageMap, false, getExperienceHeader()),
                                   createLatexFile(evaluation, statistics, recordsCount, pageMap, true, getExperienceHeader()),
                                   createHtmlFile(evaluation, statistics, recordsCount, pageMap, getExperienceHeader()));
   }
   
   protected abstract String getExperienceHeader();
   
   private AdditionalFile createLatexFile(AbstractEvaluation evaluation, 
                                          Statistics statistics, 
                                          Map<IStatisticsFilter, BigInteger> recordsCount, 
                                          Map<AbstractPage, PageStatistic> pageMap,
                                          boolean multiPage,
                                          String experienceHeader) {
      StringBuffer latex = new StringBuffer();
      latex.append("\\begin{tabularx}{1.0\\textwidth}{lXXrrrrrrrr}" + StringUtil.NEW_LINE);
      if (multiPage) {
         latex.append("\\caption{Comparison of the Given Expected Answers} \\\\" + StringUtil.NEW_LINE);
      }
      latex.append("\\toprule" + StringUtil.NEW_LINE);
      latex.append("\\multirow{3}{*}{\\rotatebox{90}{\\parbox{1.4cm}{Proof Attempt}}}&&&\\multicolumn{8}{c}{" + experienceHeader + "}\\\\" + StringUtil.NEW_LINE);
      latex.append("&&");
      for (IStatisticsFilter filter : statistics.getFilters()) {
         latex.append("& \\multicolumn{2}{c}{" + filter.getLatexName() + " (" + recordsCount.get(filter) + ")}");
      }
      latex.append("\\\\" + StringUtil.NEW_LINE);
      latex.append("& Question & Answer");
      for (@SuppressWarnings("unused") IStatisticsFilter filter : statistics.getFilters()) {
         for (Tool tool : evaluation.getTools()) {
            latex.append("&\\rotatebox{90}{" + tool.getLatexName() + "~(\\%)}");
         }
      }
      latex.append("\\\\" + StringUtil.NEW_LINE);
      Map<IStatisticsFilter, Map<Tool, BigInteger>> winningMap = new HashMap<IStatisticsFilter, Map<Tool, BigInteger>>();
      boolean afterFirst = false;
      for (PageStatistic ps : pageMap.values()) {
         latex.append("\\midrule" + StringUtil.NEW_LINE);
         if (!afterFirst) {
            if (multiPage) {
               latex.append("\\endhead" + StringUtil.NEW_LINE);
            }
            afterFirst = true;
         }
         Collection<QuestionStatistic> qss = ps.getQuestionStatistics();
         boolean pagePrinted = false;
         for (QuestionStatistic qs : qss) {
            boolean questionPrinted = false;
            Collection<ChoiceStatistic> css = qs.getChoiceStatistics();
            for (ChoiceStatistic cs : css) {
               if (!pagePrinted) {
                  int choicesCount = 0;
                  for (QuestionStatistic currentQs : qss) {
                     choicesCount += currentQs.getChoiceStatistics().size();
                  }
                  latex.append("\\multirow{" + choicesCount + "}{*}{\\rotatebox{90}{\\parbox{1.4cm}{" + ps.getPage().getLatexTitle() + "}}}");
                  pagePrinted = true;
               }
               if (!questionPrinted) {
                  latex.append(" & \\multirow{" + css.size() + "}{*}{" + qs.getQuestion().getLatexLabel() + "}");
                  questionPrinted = true;
               }
               else {
                  latex.append("&");
               }
               latex.append("&" + cs.getChoice().getLatexText());
               for (IStatisticsFilter filter : statistics.getFilters()) {
                  List<Tool> winningTools = cs.computeWinningTools(filter, evaluation.getTools());
                  if (winningTools != null && winningTools.size() == 1) {
                     Map<Tool, BigInteger> filterMap = winningMap.get(filter);
                     if (filterMap == null) {
                        filterMap = new HashMap<Tool, BigInteger>();
                        winningMap.put(filter, filterMap);
                     }
                     BigInteger currentValue = filterMap.get(winningTools.get(0));
                     if (currentValue == null) {
                        currentValue = BigInteger.ONE;
                     }
                     else {
                        currentValue = currentValue.add(BigInteger.ONE);
                     }
                     filterMap.put(winningTools.get(0), currentValue);
                  }
                  for (Tool tool : evaluation.getTools()) {
                     Statistic s = cs.getStatistic(filter, tool);
                     BigDecimal percentage = s.computePercentage(0);
                     if (winningTools != null && winningTools.size() == 1 && winningTools.contains(tool)) {
                        latex.append("&\\textcolor{blue}{" + (percentage != null ? percentage : "") + "}");
                     }
                     else {
                        latex.append("&" + (percentage != null ? percentage : ""));
                     }
                  }
               }
               latex.append("\\\\" + StringUtil.NEW_LINE);
            }
         }
      }
      latex.append("\\midrule");
      latex.append("\\multicolumn{3}{r}{\\textbf{Winning Tool Count}} ");
      for (IStatisticsFilter filter : statistics.getFilters()) {
         Map<Tool, BigInteger> filterMap = winningMap.get(filter);
         List<Tool> winningTools = new LinkedList<Tool>();
         if (filterMap != null) {
            BigInteger winningCount = null;
            for (Tool tool : evaluation.getTools()) {
               BigInteger current = filterMap.get(tool);
               if (current == null) {
                  current = BigInteger.ZERO;
               }
               if (winningCount == null) {
                  winningTools.add(tool);
                  winningCount = current;
               }
               else {
                  if (winningCount.compareTo(current) == 0) {
                     winningTools.add(tool);
                  }
                  else if (winningCount.compareTo(current) < 0) {
                     winningTools.clear();
                     winningTools.add(tool);
                     winningCount = current;
                  }
               }
            }
         }
         for (Tool tool : evaluation.getTools()) {
            BigInteger value = filterMap != null ? filterMap.get(tool) : null;
            if (winningTools.size() == 1 && winningTools.contains(tool)) {
               latex.append("&\\textbf{\\textcolor{blue}{" + (value != null ? value : BigInteger.ZERO) + "}}");
            }
            else {
               latex.append("&\\textbf{" + (value != null ? value : BigInteger.ZERO) + "}");
            }
         }
      }
      latex.append("\\\\" + StringUtil.NEW_LINE);
      latex.append("\\bottomrule" + StringUtil.NEW_LINE);
      if (multiPage) {
         latex.append("\\label{tab:rcExpectedAnswerToolComparision}");
      }
      latex.append("\\end{tabularx}" + StringUtil.NEW_LINE);
      String fileName = multiPage ?
                        "_ExpectedAnswersComparison_MultiPage.tex" :
                        "_ExpectedAnswersComparison.tex";
      return new AdditionalFile(fileName, latex.toString().getBytes(IOUtil.DEFAULT_CHARSET));
   }

   private AdditionalFile createHtmlFile(AbstractEvaluation evaluation, 
                                         Statistics statistics, 
                                         Map<IStatisticsFilter, BigInteger> recordsCount, 
                                         Map<AbstractPage, PageStatistic> pageMap,
                                         String experienceHeader) {
      StringBuffer html = new StringBuffer();
      html.append("<table border=\"0\" cellpadding=\"3\" cellspacing=\"2\">" + StringUtil.NEW_LINE);
      html.append("<tr style=\"background-color: #4e9ad6;font-weight: bold;\">" + StringUtil.NEW_LINE);
      html.append("<td colspan=\"3\" rowspan=\"2\">&nbsp;</td>" + StringUtil.NEW_LINE);
      html.append("<td colspan=\"8\" align=\"center\">" + experienceHeader + " (%)</td>" + StringUtil.NEW_LINE);
      html.append("</tr>");
      html.append("<tr style=\"background-color: #4e9ad6;font-weight: bold;\">" + StringUtil.NEW_LINE);
      for (IStatisticsFilter filter : statistics.getFilters()) {
         //html.append("<td colspan=\"2\" align=\"center\">" + filter.getLatexName() + " (" + recordsCount.get(filter) + ")</td>" + StringUtil.NEW_LINE);
         html.append("<td colspan=\"2\" align=\"center\">" + filter.getLatexName() + "</td>" + StringUtil.NEW_LINE);
      }
      html.append("</tr>");
      html.append("<tr style=\"background-color: #4e9ad6;font-weight: bold;\">" + StringUtil.NEW_LINE);
      html.append("<td>Example</td>" + StringUtil.NEW_LINE);
      html.append("<td>Question</td>" + StringUtil.NEW_LINE);
      html.append("<td>Answer</td>" + StringUtil.NEW_LINE);
      for (@SuppressWarnings("unused") IStatisticsFilter filter : statistics.getFilters()) {
         for (Tool tool : evaluation.getTools()) {
            html.append("<td>" + tool.getLatexName() + "</td>" + StringUtil.NEW_LINE);
         }
      }
      html.append("</tr>");
      Map<IStatisticsFilter, Map<Tool, BigInteger>> winningMap = new HashMap<IStatisticsFilter, Map<Tool, BigInteger>>();
      boolean afterFirst = false;
      for (PageStatistic ps : pageMap.values()) {
         if (!afterFirst) {
            afterFirst = true;
         }
         Collection<QuestionStatistic> qss = ps.getQuestionStatistics();
         boolean pagePrinted = false;
         for (QuestionStatistic qs : qss) {
            boolean questionPrinted = false;
            Collection<ChoiceStatistic> css = qs.getChoiceStatistics();
            for (ChoiceStatistic cs : css) {
               html.append("<tr style=\"background-color: #b1d3ec;\">" + StringUtil.NEW_LINE);
               if (!pagePrinted) {
                  int choicesCount = 0;
                  for (QuestionStatistic currentQs : qss) {
                     choicesCount += currentQs.getChoiceStatistics().size();
                  }
                  html.append("<td rowspan=\"" + choicesCount + "\">" + ps.getPage().getLatexTitle() + "</td>" + StringUtil.NEW_LINE);
                  pagePrinted = true;
               }
               if (!questionPrinted) {
                  html.append("<td rowspan=\"" + css.size() + "\">" + qs.getQuestion().getLatexLabel() + "</td>" + StringUtil.NEW_LINE);
                  questionPrinted = true;
               }
               html.append("<td>" + cs.getChoice().getLatexText() + "</td>" + StringUtil.NEW_LINE);
               for (IStatisticsFilter filter : statistics.getFilters()) {
                  List<Tool> winningTools = cs.computeWinningTools(filter, evaluation.getTools());
                  if (winningTools != null && winningTools.size() == 1) {
                     Map<Tool, BigInteger> filterMap = winningMap.get(filter);
                     if (filterMap == null) {
                        filterMap = new HashMap<Tool, BigInteger>();
                        winningMap.put(filter, filterMap);
                     }
                     BigInteger currentValue = filterMap.get(winningTools.get(0));
                     if (currentValue == null) {
                        currentValue = BigInteger.ONE;
                     }
                     else {
                        currentValue = currentValue.add(BigInteger.ONE);
                     }
                     filterMap.put(winningTools.get(0), currentValue);
                  }
                  for (Tool tool : evaluation.getTools()) {
                     Statistic s = cs.getStatistic(filter, tool);
                     BigDecimal percentage = s.computePercentage(0);
                     if (winningTools != null && winningTools.size() == 1 && winningTools.contains(tool)) {
                        html.append("<td style=\"color: blue;\">" + (percentage != null ? percentage : "&nbsp;") + "</td>" + StringUtil.NEW_LINE);
                     }
                     else {
                        html.append("<td>" + (percentage != null ? percentage : "&nbsp;") + "</td>" + StringUtil.NEW_LINE);
                     }
                  }
               }
               html.append("</tr>" + StringUtil.NEW_LINE);
            }
         }
      }
      html.append("<tr style=\"background-color: #b1d3ec; font-weight: bold;\">" + StringUtil.NEW_LINE);
      html.append("<td colspan=\"3\" align=\"right\">Winning Tool Count</td>" + StringUtil.NEW_LINE);
      for (IStatisticsFilter filter : statistics.getFilters()) {
         Map<Tool, BigInteger> filterMap = winningMap.get(filter);
         List<Tool> winningTools = new LinkedList<Tool>();
         if (filterMap != null) {
            BigInteger winningCount = null;
            for (Tool tool : evaluation.getTools()) {
               BigInteger current = filterMap.get(tool);
               if (current == null) {
                  current = BigInteger.ZERO;
               }
               if (winningCount == null) {
                  winningTools.add(tool);
                  winningCount = current;
               }
               else {
                  if (winningCount.compareTo(current) == 0) {
                     winningTools.add(tool);
                  }
                  else if (winningCount.compareTo(current) < 0) {
                     winningTools.clear();
                     winningTools.add(tool);
                     winningCount = current;
                  }
               }
            }
         }
         for (Tool tool : evaluation.getTools()) {
            BigInteger value = filterMap != null ? filterMap.get(tool) : null;
            if (winningTools.size() == 1 && winningTools.contains(tool)) {
               html.append("<td style=\"color: blue;\">" + (value != null ? value : BigInteger.ZERO) + "</td>" + StringUtil.NEW_LINE);
            }
            else {
               html.append("<td>" + (value != null ? value : BigInteger.ZERO) + "</td>" + StringUtil.NEW_LINE);
            }
         }
      }
      html.append("</tr>" + StringUtil.NEW_LINE);
      html.append("</table>" + StringUtil.NEW_LINE);
      String fileName = "_ExpectedAnswersComparison.html";
      return new AdditionalFile(fileName, html.toString().getBytes(IOUtil.DEFAULT_CHARSET));
   }

   private static class PageStatistic {
      private final AbstractPage page;
      private final Map<AbstractQuestion, QuestionStatistic> questionMap = new LinkedHashMap<AbstractQuestion, QuestionStatistic>();

      public PageStatistic(AbstractPage page) {
         this.page = page;
      }
      
      public AbstractPage getPage() {
         return page;
      }

      public QuestionStatistic getQuestionStatistic(AbstractQuestion question) {
         QuestionStatistic questionStatistic = questionMap.get(question);
         if (questionStatistic == null) {
            questionStatistic = new QuestionStatistic(question);
            questionMap.put(question, questionStatistic);
         }
         return questionStatistic;
      }
      
      public Collection<QuestionStatistic> getQuestionStatistics() {
         return questionMap.values();
      }
   }
   
   private static class QuestionStatistic {
      private final AbstractQuestion question;
      private final Map<Choice, ChoiceStatistic> choiceMap = new LinkedHashMap<Choice, ChoiceStatistic>();

      public QuestionStatistic(AbstractQuestion question) {
         this.question = question;
      }
      
      public AbstractQuestion getQuestion() {
         return question;
      }

      public ChoiceStatistic getChoiceStatistic(Choice choice) {
         ChoiceStatistic choiceStatistic = choiceMap.get(choice);
         if (choiceStatistic == null) {
            choiceStatistic = new ChoiceStatistic(choice);
            choiceMap.put(choice, choiceStatistic);
         }
         return choiceStatistic;
      }
      
      public Collection<ChoiceStatistic> getChoiceStatistics() {
         return choiceMap.values();
      }
   }
   
   private static class ChoiceStatistic {
      private final Choice choice;
      private final Map<IStatisticsFilter, Map<Tool, Statistic>> filterMap = new LinkedHashMap<IStatisticsFilter, Map<Tool, Statistic>>();

      public ChoiceStatistic(Choice choice) {
         this.choice = choice;
      }

      public Choice getChoice() {
         return choice;
      }

      public Statistic getStatistic(IStatisticsFilter filter, Tool tool) {
         Map<Tool, Statistic> toolMap = filterMap.get(filter);
         if (toolMap == null) {
            toolMap = new LinkedHashMap<Tool, Statistic>();
            filterMap.put(filter, toolMap);
         }
         Statistic statistic = toolMap.get(tool);
         if (statistic == null) {
            statistic = new Statistic();
            toolMap.put(tool, statistic);
         }
         return statistic;
      }
      
      public List<Tool> computeWinningTools(IStatisticsFilter filter, Tool[] tools) {
         List<Tool> winners = new LinkedList<Tool>();
         BigDecimal winnersPercentage = null;
         for (Tool tool : tools) {
            Statistic s = getStatistic(filter, tool);
            BigDecimal current = s.computePercentage();
            if (current == null) {
               return null; // No winning tool available as records for tool are missing.
            }
            if (winnersPercentage == null) {
               winners.add(tool);
               winnersPercentage = current;
            }
            else {
               if (winnersPercentage.compareTo(current) == 0) {
                  winners.add(tool);
               }
               else if (winnersPercentage.compareTo(current) < 0) {
                  winners.clear();
                  winners.add(tool);
                  winnersPercentage = current;
               }
            }
         }
         return winners;
      }
   }
   
   private static class Statistic {
      private BigInteger selectedCount = BigInteger.ZERO;
      private BigInteger maxCount = BigInteger.ZERO;
      
      public void update(boolean selected) {
         if (selected) {
            selectedCount = selectedCount.add(BigInteger.ONE);
         }
         maxCount = maxCount.add(BigInteger.ONE);
      }

      public BigDecimal computePercentage() {
         return computePercentage(2);
      }

      public BigDecimal computePercentage(int decimalDigits) {
         BigInteger mul100 = selectedCount.multiply(BigInteger.valueOf(100));
         if (!maxCount.equals(BigInteger.ZERO)) {
            return new BigDecimal(mul100).divide(new BigDecimal(maxCount), decimalDigits, RoundingMode.HALF_EVEN);
         }
         else {
            return null;
         }
      }
   }

   private List<AbstractQuestion> listQuestionsWithResults(AbstractPage page) {
      List<AbstractQuestion> result = new LinkedList<AbstractQuestion>();
      if (page instanceof QuestionPage) {
         for (AbstractQuestion question : ((QuestionPage) page).getQuestions()) {
            dolistQuestionsWithResults(question, result);
         }
      }
      return result;
   }

   private void dolistQuestionsWithResults(AbstractQuestion question, List<AbstractQuestion> result) {
      if (question instanceof AbstractChoicesQuestion) {
         if (question.isEnabled()) {
            if (!CollectionUtil.isEmpty(((AbstractChoicesQuestion) question).getCorrectChoices())) {
               result.add(question);
            }
            for (Choice choice :  ((AbstractChoicesQuestion) question).getChoices()) {
               for (AbstractQuestion child : choice.getChildQuestions()) {
                  dolistQuestionsWithResults(child, result);
               }
            }
         }
      }
      if (question instanceof IQuestionWithCildren) {
         for (AbstractQuestion child : ((IQuestionWithCildren) question).getChildQuestions()) {
            dolistQuestionsWithResults(child, result);
         }
      }
   }
}