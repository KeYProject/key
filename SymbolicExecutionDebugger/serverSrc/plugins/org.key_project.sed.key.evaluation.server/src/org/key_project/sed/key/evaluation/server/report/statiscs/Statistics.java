package org.key_project.sed.key.evaluation.server.report.statiscs;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractChoicesQuestion;
import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Choice;
import org.key_project.sed.key.evaluation.model.definition.IQuestionWithCildren;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.AbstractReportEngine;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

/**
 * The statistics computed by {@link AbstractReportEngine#computeStatistics(AbstractEvaluation, EvaluationResult)}.
 * @author Martin Hentschel
 */
public class Statistics {
   /**
    * The contained {@link FilteredStatistics}.
    */
   private final Map<IStatisticsFilter, FilteredStatistics> filteredStatiscs = new LinkedHashMap<IStatisticsFilter, FilteredStatistics>();

   /**
    * Checks if multiple answers were ignored.
    */
   private boolean multipleValuedAnswersIgnored;
   
   /**
    * Constructor.
    * @param filters The available {@link IStatisticsFilter}.
    * @param result The {@link EvaluationResult} to analyze.
    */
   public Statistics(IStatisticsFilter[] filters, EvaluationResult result) {
      for (IStatisticsFilter filter : filters) {
         filteredStatiscs.put(filter, new FilteredStatistics());
      }
      for (EvaluationAnswers answer : result.getIdInputMap().values()) {
         if (!answer.hasMultipleValues()) {
            for (IStatisticsFilter filter : filters) {
               if (filter.accept(answer)) {
                  FilteredStatistics filteredStatistics = filteredStatiscs.get(filter);
                  filteredStatistics.updateAnswersCount();
                  for (AbstractQuestion question : answer.getQuestions()) {
                     initQuestion(filteredStatistics, answer, question);
                  }
                  for (AbstractPage page : answer.getPages()) {
                     List<AbstractPageInput<?>> pageInputs = answer.getPageInputs(page);
                     if (!CollectionUtil.isEmpty(pageInputs)) {
                        if (pageInputs.size() > 1) {
                           throw new IllegalStateException("Multiple page inputs found.");
                        }
                        AbstractPageInput<?> pageInput = pageInputs.get(0);
                        if (pageInput.getPage().isToolBased()) {
                           List<Tool> tools = answer.getTools(pageInput.getPage());
                           if (tools != null) {
                              if (tools.size() > 1) {
                                 throw new IllegalStateException("Multiple tools found.");
                              }
                              filteredStatistics.update(pageInput, tools.get(0));
                           }
                        }
                        else {
                           filteredStatistics.update(pageInput, null);
                        }
                     }
                  }
               }
            }
         }
         else {
            multipleValuedAnswersIgnored = true;
         }
      }
   }
  
   /**
    * Initializes the statistics of the given {@link AbstractQuestion}.
    * @param filteredStatistics The current {@link FilteredStatistics}.
    * @param answer The current {@link EvaluationAnswers}.
    * @param question The current {@link AbstractQuestion}.
    */
   private void initQuestion(FilteredStatistics filteredStatistics, EvaluationAnswers answer, AbstractQuestion question) {
      if (question.isEditable() && question.isEnabled()) {
         List<QuestionInput> questionInputs = answer.getQuestionInputs(question);
         if (!CollectionUtil.isEmpty(questionInputs)) {
            if (questionInputs.size() > 1) {
               throw new IllegalStateException("Multiple question inputs found.");
            }
            QuestionInput questionInput = questionInputs.get(0);
            if (questionInput.getPageInput().getPage().isToolBased()) {
               List<Tool> tools = answer.getTools(questionInput.getPageInput().getPage());
               if (tools != null) {
                  if (tools.size() > 1) {
                     throw new IllegalStateException("Multiple tools found.");
                  }
                  filteredStatistics.update(questionInput, tools.get(0));
               }
            }
            else {
               filteredStatistics.update(questionInput, null);
            }
         }
      }
      // Child questions
      if (question instanceof AbstractChoicesQuestion) {
         AbstractChoicesQuestion choiceQuestion = (AbstractChoicesQuestion) question;
         if (choiceQuestion.hasChildQuestions()) {
            for (Choice choice : choiceQuestion.getChoices()) {
               if (choice.countChildQuestions() > 0) {
                  for (AbstractQuestion cildQuestion : choice.getChildQuestions()) {
                     initQuestion(filteredStatistics, answer, cildQuestion);
                  }
               }
            }
         }
      }
      else if (question instanceof IQuestionWithCildren) {
         IQuestionWithCildren withChildrenQuestion = (IQuestionWithCildren) question;
         if (withChildrenQuestion.countChildQuestions() > 0) {
            for (AbstractQuestion cildQuestion : withChildrenQuestion.getChildQuestions()) {
               initQuestion(filteredStatistics, answer, cildQuestion);
            }
         }
      }
   }
   
   /**
    * Returns the available {@link IStatisticsFilter}s.
    * @return The available {@link IStatisticsFilter}s.
    */
   public Set<IStatisticsFilter> getFilters() {
      return filteredStatiscs.keySet();
   }
   
   /**
    * Returns the {@link FilteredStatistics} of the given {@link IStatisticsFilter}.
    * @param filter The {@link IStatisticsFilter} for which {@link FilteredStatistics} are requested.
    * @return The {@link FilteredStatistics}.
    */
   public FilteredStatistics getFilteredStatistics(IStatisticsFilter filter) {
      return filteredStatiscs.get(filter);
   }

   /**
    * Checks if answers with multiple values were ignored.
    * @return {@code true} some answers are ignored, {@code true} all answers are considered.
    */
   public boolean isMultipleValuedAnswersIgnored() {
      return multipleValuedAnswersIgnored;
   }
   
   /**
    * Checks if at least one of the {@link FilteredStatistics} contains
    * {@link PageStatistics} for the given {@link AbstractPage}.
    * @param page The {@link AbstractPage} to check.
    * @return {@code true} {@link PageStatistics} available, {@code false} {@link PageStatistics} not available.
    */
   public boolean containsToolPageStatistics(final AbstractPage page) {
      return CollectionUtil.search(getFilters(), new IFilter<IStatisticsFilter>() {
         @Override
         public boolean select(IStatisticsFilter element) {
            FilteredStatistics fs = filteredStatiscs.get(element);
            boolean toolQuestion = false;
            Iterator<Tool> toolsIter = fs.getTools().iterator();
            while (!toolQuestion && toolsIter.hasNext()) {
               Tool tool = toolsIter.next();
               if (fs.getPageStatistics(tool).containsKey(page)) {
                  toolQuestion = true;
               }
            }
            return toolQuestion;
         }
      }) != null;
   }

   /**
    * Checks if at least one of the {@link FilteredStatistics} contains
    * {@link QuestionStatistics} for the given {@link AbstractQuestion}.
    * @param question The {@link AbstractQuestion} to check.
    * @return {@code true} {@link QuestionStatistics} available, {@code false} {@link QuestionStatistics} not available.
    */
   public boolean containsToolQuestionStatistics(final AbstractQuestion question) {
      return CollectionUtil.search(getFilters(), new IFilter<IStatisticsFilter>() {
         @Override
         public boolean select(IStatisticsFilter element) {
            FilteredStatistics fs = filteredStatiscs.get(element);
            boolean toolQuestion = false;
            Iterator<Tool> toolsIter = fs.getTools().iterator();
            while (!toolQuestion && toolsIter.hasNext()) {
               Tool tool = toolsIter.next();
               if (fs.getQuestionStatistics(tool).containsKey(question)) {
                  toolQuestion = true;
               }
            }
            return toolQuestion;
         }
      }) != null;
   }

   /**
    * Checks if at least one {@link ChoiceStatistics} is available.
    * @param question The {@link AbstractQuestion} to check.
    * @return {@code true} {@link ChoiceStatistics} available, {@code false} {@link ChoiceStatistics} not available.
    */
   public boolean containsChoiceStatistics(final AbstractQuestion question) {
      if (question instanceof AbstractChoicesQuestion) {
         return CollectionUtil.search(getFilters(), new IFilter<IStatisticsFilter>() {
            @Override
            public boolean select(IStatisticsFilter element) {
               FilteredStatistics fs = filteredStatiscs.get(element);
               Map<Choice, ChoiceStatistics> choiceMap = fs.getChoiceStatistics((AbstractChoicesQuestion) question);
               return !CollectionUtil.isEmpty(choiceMap);
            }
         }) != null;
      }
      else {
         return false;
      }
   }
}