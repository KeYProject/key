package org.key_project.sed.key.evaluation.server.report.statiscs;

import java.math.BigInteger;

import org.key_project.sed.key.evaluation.model.definition.AbstractPage;
import org.key_project.sed.key.evaluation.model.input.AbstractPageInput;

/**
 * The statics of an {@link AbstractPage}.
 * @author Martin Hentschel
 */
public class PageStatistics {
   /**
    * Counts how {@link #timesSum} was updated.
    */
   private BigInteger timesCount = BigInteger.ZERO;

   /**
    * The sum of all {@link AbstractPageInput#getShownTime()} values.
    */
   private BigInteger timesSum = BigInteger.ZERO;
   
   /**
    * Updates the statics.
    * @param time The time.
    */
   protected void update(long time) {
      if (time > 0) {
         timesCount = timesCount.add(BigInteger.ONE); 
         timesSum = timesSum.add(BigInteger.valueOf(time));
      }
   }

   /**
    * Returns how often {@link #getTimesSum()} was updated.
    * @return The value.
    */
   public BigInteger getTimesCount() {
      return timesCount;
   }

   /**
    * Returns the sum of all {@link AbstractPageInput#getShownTime()} values.
    * @return The value.
    */
   public BigInteger getTimesSum() {
      return timesSum;
   }
   
   /**
    * Computes the average time.
    * @return The average time.
    */
   public BigInteger computeAverageTime() {
      if (!BigInteger.ZERO.equals(timesCount)) {
         return timesSum.divide(timesCount);
      }
      else {
         return BigInteger.ZERO;
      }
   }
}