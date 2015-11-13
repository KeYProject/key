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

public class HTMLExpectedAnswersComparison implements IHTMLSectionAppender {
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
                     Tool tool = entry.getValue().getTools(page).get(0);
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
                  sb.append("<td rowspan=\"" + choicesCount + "\" valign=\"top\">" + ps.getPage().getName() + "</td>");
                  pagePrinted = true;
               }
               if (!questionPrinted) {
                  sb.append("<td rowspan=\"" + css.size() + "\" valign=\"top\">" + qs.getQuestion().getName() + "</td>");
                  questionPrinted = true;
               }
               sb.append("<td>" + cs.getChoice().getText() + "</td>");
               for (IStatisticsFilter filter : statistics.getFilters()) {
                  List<Tool> winningTools = cs.computeWinningTools(filter, evaluation.getTools());
                  if (winningTools.size() == 1) {
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
                     if (winningTools.contains(tool)) {
                        String color = winningTools.size() == 1 ?
                                       "blue" :
                                       "#FF00FF";
                        sb.append("<td align=\"right\"><font color=\"" + color + "\">" + s.computePercentage() + "</font></td>");
                     }
                     else {
                        sb.append("<td align=\"right\">" + s.computePercentage() + "</td>");
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
      return null;
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
            if (winnersPercentage == null) {
               winners.add(tool);
               winnersPercentage = s.computePercentage();
            }
            else {
               BigDecimal current = s.computePercentage();
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
         BigInteger mul100 = selectedCount.multiply(BigInteger.valueOf(100));
         return new BigDecimal(mul100).divide(new BigDecimal(maxCount), 2, RoundingMode.HALF_EVEN);
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
         if (!CollectionUtil.isEmpty(((AbstractChoicesQuestion) question).getCorrectChoices())) {
            result.add(question);
         }
         for (Choice choice :  ((AbstractChoicesQuestion) question).getChoices()) {
            for (AbstractQuestion child : choice.getChildQuestions()) {
               dolistQuestionsWithResults(child, result);
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
