package org.key_project.sed.key.evaluation.server.report.html;

/**
 * Exports the knowledge of the participants as LaTeX file.
 * @author Martin Hentschel
 */
public class ReviewingCodeExpectedAnswersComparison extends AbstractExpectedAnswersComparison {
   /**
    * {@inheritDoc}
    */
   @Override
   protected String getExperienceHeader() {
      return "\\Java experience";
   }
}
