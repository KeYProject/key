package org.key_project.sed.key.evaluation.server.report.statiscs;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.key_project.sed.key.evaluation.model.definition.AbstractEvaluation;
import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.definition.Tool;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;
import org.key_project.sed.key.evaluation.server.report.AbstractReportEngine;
import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;
import org.key_project.sed.key.evaluation.server.report.EvaluationResult;
import org.key_project.sed.key.evaluation.server.report.filter.IStatisticsFilter;
import org.key_project.util.java.CollectionUtil;

/**
 * The statistics computed by {@link AbstractReportEngine#computeStatistics(AbstractEvaluation, EvaluationResult)}.
 * @author Martin Hentschel
 */
public class Statistics {
   /**
    * The contained {@link FilteredStatistics}.
    */
   private final Map<IStatisticsFilter, FilteredStatistics> filteredStatiscs = new HashMap<IStatisticsFilter, FilteredStatistics>();

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
                  for (AbstractQuestion question : answer.getQuestions()) {
                     if (question.isEditable()) {
                        List<QuestionInput> questionInputs = answer.getQuestionInputs(question);
                        if (!CollectionUtil.isEmpty(questionInputs)) {
                           if (questionInputs.size() > 1) {
                              throw new IllegalStateException("Multiple question inputs found.");
                           }
                           QuestionInput questionInput = questionInputs.get(0);
                           if (questionInput.getPageInput().getPage().isToolBased()) {
                              List<Tool> tools = answer.getTools(questionInput.getPageInput().getPage());
                              if (tools == null) {
                                 throw new IllegalStateException("Tools are missing.");
                              }
                              if (tools.size() > 1) {
                                 throw new IllegalStateException("Multiple tools found.");
                              }
                              filteredStatistics.update(questionInput, tools.get(0));
                           }
                           else {
                              filteredStatistics.update(questionInput, null);
                           }
                        }
                     }
                  }
                  for (AbstractPage page : answer.getPages()) {
                     List<AbstractPageInput<?>> pageInputs = answer.getPageInputs(page);
                     if (!CollectionUtil.isEmpty(pageInputs)) {
                        if (pageInputs.size() > 1) {
                           throw new IllegalStateException("Multiple page inputs found.");
                        }
                        AbstractPageInput<?> pageInput = pageInputs.get(0);
                        filteredStatistics.update(pageInput);
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
}