package org.key_project.sed.key.evaluation.server.report.filter;

import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;

/**
 * An {@link IStatisticsFilter} is used to select {@link EvaluationAnswers}
 * to consider.
 * <p>
 * Implementations should subclass from {@link AbstractStatisticsFilter}.
 * @author Martin Hentschel
 */
public interface IStatisticsFilter {
   /**
    * Returns the name of the filter.
    * @return The filter name.
    */
   public String getName();
   
   /**
    * Returns the name shown in latex files.
    * @return The name shown in latex files.
    */
   public String getLatexName();
   
   /**
    * Checks if the {@link EvaluationAnswers} should be considered or not.
    * @param answer The {@link EvaluationAnswers} to check.
    * @return {@code true} include in statistics, {@code false} ignore in statistics.
    */
   public boolean accept(EvaluationAnswers answer);
}
