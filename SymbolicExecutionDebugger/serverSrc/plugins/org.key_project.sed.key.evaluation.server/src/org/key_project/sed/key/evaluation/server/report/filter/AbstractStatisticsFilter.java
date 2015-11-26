package org.key_project.sed.key.evaluation.server.report.filter;

/**
 * Provides a basic implementation of {@link IStatisticsFilter}.
 * @author Martin Hentschel
 */
public abstract class AbstractStatisticsFilter implements IStatisticsFilter {
   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getName();
   }
}
