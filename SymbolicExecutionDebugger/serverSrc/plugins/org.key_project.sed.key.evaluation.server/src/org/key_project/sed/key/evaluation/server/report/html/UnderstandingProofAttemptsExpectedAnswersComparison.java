package org.key_project.sed.key.evaluation.server.report.html;

/**
 * Exports the knowledge of the participants as LaTeX file.
 * @author Martin Hentschel
 */
public class UnderstandingProofAttemptsExpectedAnswersComparison extends AbstractExpectedAnswersComparison {
   /**
    * {@inheritDoc}
    */
   @Override
   protected String getExperienceHeader() {
      return "\\KeY experience";
   }
}
