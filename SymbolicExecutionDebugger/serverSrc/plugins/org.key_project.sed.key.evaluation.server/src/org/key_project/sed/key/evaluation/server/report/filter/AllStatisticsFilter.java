package org.key_project.sed.key.evaluation.server.report.filter;

import org.key_project.sed.key.evaluation.server.report.EvaluationAnswers;

/**
 * An {@link IStatisticsFilter} which includes all {@link EvaluationAnswers}.
 * @author Martin Hentschel
 */
public class AllStatisticsFilter extends AbstractStatisticsFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "All Answers";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getLatexName() {
      return "All";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean accept(EvaluationAnswers answer) {
      return true;
   }
}