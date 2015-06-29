package org.key_project.sed.key.evaluation.server.report.statiscs;

import java.math.BigInteger;

import org.key_project.sed.key.evaluation.model.definition.Choice;

/**
 * The statics of a {@link Choice}.
 * @author Martin Hentschel
 */
public class ChoiceStatistics {
   /**
    * Counts how often the {@link Choice} is selected.
    */
   private BigInteger selectedCount = BigInteger.ZERO;

   /**
    * Updates {@link #getSelectedCount()} by {@code 1}.
    */
   protected void update() {
      selectedCount = selectedCount.add(BigInteger.ONE);
   }

   /**
    * Returns how often the {@link Choice} is selected.
    * @return how often the {@link Choice} is selected.
    */
   public BigInteger getSelectedCount() {
      return selectedCount;
   }
}
