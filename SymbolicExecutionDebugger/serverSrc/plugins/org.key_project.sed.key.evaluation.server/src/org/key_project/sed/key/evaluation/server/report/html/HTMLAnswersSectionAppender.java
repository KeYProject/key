package org.key_project.sed.key.evaluation.server.report.html;

import java.io.File;
import java.text.DateFormat;
import java.util.Collection;
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
import org.key_project.sed.key.evaluation.model.definition.IQuestionWithCildren;
import org.key_project.sed.key.evaluation.model.definition.QuestionPage;
import org.key_project.sed.key.evaluation.model.definition.RandomForm;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractFormInput;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.model.input.Trust;
import org.key_project.sed.key.evaluation.server.report.AdditionalFile;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.statiscs.Statistics;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.StringUtil;

/**
 * Appends the received answers section.
 * @author Martin Hentschel
 */
public class HTMLAnswersSectionAppender implements IHTMLSectionAppender {
   /**
    * {@inheritDoc}
    */
   @Override
   public Collection<AdditionalFile> appendSection(File storageLocation, AbstractEvaluation evaluation, EvaluationResult result, Statistics statistics, StringBuffer sb) {
      // Append table header
      sb.append("<h1><a name=\"answers\">Received Answers</a></h1>");
      sb.append("<table border=\"1\">");
      // Append header
      List<Object> questionOrder = new LinkedList<Object>();
      appendReceivedAnswersResultsHeader(evaluation, sb, questionOrder);
      // Append expected answers
      sb.append("<tr>");
      sb.append("<td><font color=\"#FF80FF\">Expected Answers</font></td>");
      for (Object object : questionOrder) {
         if (object instanceof AbstractQuestion) {
            AbstractQuestion question = (AbstractQuestion) object;
            if (question.isEditable() && question.isEnabled()) {
               if (question instanceof AbstractChoicesQuestion) {
                  AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
                  Set<Choice> correctChoices = choiceQuestion.getCorrectChoices();
                  if (!CollectionUtil.isEmpty(correctChoices)) {
                     sb.append("<td><font color=\"#FF80FF\">");
                     boolean afterFirst = false;
                     for (Choice choice : correctChoices) {
                        if (afterFirst) {
                           sb.append(AbstractChoicesQuestion.VALUE_SEPARATOR);
                        }
                        else {
                           afterFirst = true;
                        }
                        sb.append(choice.getValue());
                     }
                     sb.append("</font></td>");
                  }
                  else {
                     sb.append("<td>&nbsp;</td>");
                  }
               }
               else {
                  sb.append("<td>&nbsp;</td>");
               }
            }
            else {
               sb.append("<td>&nbsp;</td>");
            }
         }
         else if (object instanceof AbstractPage) {
            AbstractPage page = (AbstractPage) object;
            if (page.getForm().isCollectTimes()) {
               sb.append("<td>&nbsp;</td>");
            }
            if (page.isToolBased()) {
               sb.append("<td>&nbsp;</td>");
            }
         }
         else if (object instanceof AbstractForm) {
            sb.append("<td>&nbsp;</td>");
         }
      }
      sb.append("</tr>");
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
                        Integer correctessScore = questionInput.computeCorrectWrongDifference();
                        if (correctessScore != null) {
                           appendReceivedAnswersTableCellValue(" {score:&nbsp;" + correctessScore + "}", correctessScore > 0, -1, sb);
                        }
                        if (questionInput.getQuestion().isAskForTrust()) {
                           sb.append(" (");
                           Trust trust = questionInput.getTrust();
                           if (trust != null) {
                              Integer trustScore = questionInput.computeTrustScore();
                              if (trustScore != null) {
                                 appendReceivedAnswersTableCellValue(trust.getName() + "&nbsp;(" + trustScore + ")", trustScore.intValue() > 0, questionInput.getTrustSetAt(), sb);
                              }
                              else {
                                 appendReceivedAnswersTableCellValue(trust.getName(), null, questionInput.getTrustSetAt(), sb);
                              }
                           }
                           else {
                              appendReceivedAnswersTableCellValue("trust&nbsp;missing", null, questionInput.getTrustSetAt(), sb);
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
      return null;
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
         sb.append("&nbsp;ms]");
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
      if (question.isEditable() && question.isEnabled()) {
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
      else if (question instanceof IQuestionWithCildren) {
         IQuestionWithCildren withChildrenQuestion = (IQuestionWithCildren) question;
         if (withChildrenQuestion.countChildQuestions() > 0) {
            for (AbstractQuestion cildQuestion : withChildrenQuestion.getChildQuestions()) {
               questionCount += appendReceivedAnswersQuestionHeader(cildQuestion, sb, questionOrder);
            }
         }
      }
      return questionCount;
   }   
}
