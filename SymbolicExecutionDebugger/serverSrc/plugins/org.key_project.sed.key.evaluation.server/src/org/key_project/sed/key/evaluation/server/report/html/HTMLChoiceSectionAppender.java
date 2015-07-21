package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractForm;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.IQuestionWithCildren;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.sed.key.evaluation.server.report.statiscs.ChoiceStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.FilteredStatistics;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.XMLUtil;

/**
 * Appends the choice section.
 * @author Martin Hentschel
 */
public class HTMLChoiceSectionAppender implements IHTMLSectionAppender {
   /**
    * {@inheritDoc}
    */
   @Override
   public void appendSection(File storageLocation, AbstractEvaluation evaluation, EvaluationResult result, Statistics statistics, StringBuffer sb) {
      sb.append("<h1><a name=\"choices\">Choices</a></h1>");
      sb.append("<table border=\"1\">");
      // Append header
      sb.append("<tr>");
      sb.append("<td rowspan=\"2\" colspan=\"4\">&nbsp;</td>");
      for (IStatisticsFilter filter : statistics.getFilters()) {
         sb.append("<td colspan=\"2\" align=\"center\"><b>");
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
         sb.append("<td><b>Count</b></td>");
         sb.append("<td><b>Percent</b></td>");
      }
      sb.append("</tr>");
      // Append content
      for (AbstractForm form : evaluation.getForms()) {
         Map<AbstractPage, Integer> questionCount = countStatistics(statistics, form);
         int formSpan = 0;
         for (Integer value : questionCount.values()) {
            formSpan += value;
         }
         if (formSpan > 0) {
            sb.append("<tr>");
            sb.append("<td rowspan=\"" + formSpan  + "\" valign=\"top\"><b>");
            sb.append(form.getName());
            sb.append("</b></td>");
            boolean firstPage = true;
            for (AbstractPage page : form.getPages()) {
               int pageSpan = questionCount.get(page);
               if (pageSpan > 0) {
                  if (!firstPage) {
                     sb.append("<tr>");
                  }
                  sb.append("<td rowspan=\"" + pageSpan + "\" valign=\"top\"><b>");
                  sb.append(page.getName());
                  sb.append("</b></td>");
                  if (page instanceof QuestionPage) {
                     QuestionPage questionPage = (QuestionPage) page;
                     boolean firstChoiceQuestion = true;
                     for (AbstractQuestion question : questionPage.getQuestions()) {
                        if (appendQuestion(evaluation, statistics, question, !firstChoiceQuestion, sb)) {
                           firstChoiceQuestion = false;
                           firstPage = false;
                        }
                     }
                  }
                  else {
                     throw new IllegalStateException("Unsupported page: " + page);
                  }
               }
            }
         }
      }
      sb.append("</table>");
      if (statistics.isMultipleValuedAnswersIgnored()) {
         sb.append("<p><a href=\"#answers\">Answers with multiple values (gray colored) are ignored.</a></p>");
      }
   }

   /**
    * Appends the choice statistics of the given {@link AbstractQuestion}.
    * @param evaluation The analyzed {@link AbstractEvaluation}.
    * @param statistics The computed {@link Statistics}.
    * @param question The {@link AbstractQuestion} to append.
    * @param sb The {@link StringBuffer} to append to.
    */
   protected boolean appendQuestion(AbstractEvaluation evaluation, Statistics statistics, AbstractQuestion question, boolean openTr, StringBuffer sb) {
      boolean questionAppended = false;
      if (question instanceof AbstractChoicesQuestion && 
          statistics.containsChoiceStatistics(question)) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (openTr) {
            sb.append("<tr>");
         }
         sb.append("<td rowspan=\"" + choiceQuestion.countChoices() + "\" valign=\"top\"><b>");
         sb.append(question.getName());
         sb.append("</b></td>");
         boolean afterFirst = false;
         for (Choice choice : choiceQuestion.getChoices()) {
            if (afterFirst) {
               sb.append("<tr>");
            }
            else {
               afterFirst = true;
            }
            sb.append("<td><b>");
            sb.append(XMLUtil.encodeText(choice.getText()));
            sb.append("</b></td>");
            for (IStatisticsFilter filter : statistics.getFilters()) {
               FilteredStatistics fs = statistics.getFilteredStatistics(filter);
               ChoiceStatistics cs = fs.getChoiceStatistics(choiceQuestion, choice);
               if (cs != null) {
                  sb.append("<td>" + cs.getSelectedCount() + "</td>");
                  sb.append("<td>" + fs.computeChoicePercent(choiceQuestion, choice) + "&nbsp%</td>");
               }
               else {
                  sb.append("<td colspan=\"2\">&nbsp;</td>");
               }
            }
            sb.append("</tr>\n");
         }
         questionAppended = true;
      }
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (choiceQuestion.hasChildQuestions()) {
            for (Choice choice : choiceQuestion.getChoices()) {
               if (choice.countChildQuestions() > 0) {
                  for (AbstractQuestion cildQuestion : choice.getChildQuestions()) {
                     if (appendQuestion(evaluation, statistics, cildQuestion, questionAppended || openTr, sb)) {
                        questionAppended = true;
                     }
                  }
               }
            }
         }
      }
      else if (question instanceof IQuestionWithCildren) {
         IQuestionWithCildren withChildrenQuestion = (IQuestionWithCildren) question;
         if (withChildrenQuestion.countChildQuestions() > 0) {
            for (AbstractQuestion cildQuestion : withChildrenQuestion.getChildQuestions()) {
               if (appendQuestion(evaluation, statistics, cildQuestion, questionAppended || openTr, sb)) {
                  questionAppended = true;
               }
            }
         }
      }
      return questionAppended;
   }
   
   /**
    * Counts the {@link ChoiceStatistics}.
    * @param statistics The {@link Statistics} to count in.
    * @param form The {@link AbstractForm} to count.
    * @return The results.
    */
   protected Map<AbstractPage, Integer> countStatistics(Statistics statistics, AbstractForm form) {
      Map<AbstractPage, Integer> result = new HashMap<AbstractPage, Integer>();
      for (AbstractPage page : form.getPages()) {
         int pageCount = 0;
         if (!page.isReadonly()) {
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
    * Counts the {@link ChoiceStatistics}.
    * @param statistics The {@link Statistics} to count in.
    * @param question The current {@link AbstractQuestion}.
    * @return The number of entries.
    */
   protected int countStatistics(Statistics statistics, AbstractQuestion question) {
      int questionCount = 0;
      if (statistics.containsChoiceStatistics(question)) {
         questionCount += ((AbstractChoicesQuestion) question).countChoices();
      }
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (choiceQuestion.hasChildQuestions()) {
            for (Choice choice : choiceQuestion.getChoices()) {
               if (choice.countChildQuestions() > 0) {
                  for (AbstractQuestion cildQuestion : choice.getChildQuestions()) {
                     questionCount += countStatistics(statistics, cildQuestion);
                  }
               }
            }
         }
      }
      else if (question instanceof IQuestionWithCildren) {
         IQuestionWithCildren withChildrenQuestion = (IQuestionWithCildren) question;
         if (withChildrenQuestion.countChildQuestions() > 0) {
            for (AbstractQuestion cildQuestion : withChildrenQuestion.getChildQuestions()) {
               questionCount += countStatistics(statistics, cildQuestion);
            }
         }
      }
      return questionCount;
   }
}
