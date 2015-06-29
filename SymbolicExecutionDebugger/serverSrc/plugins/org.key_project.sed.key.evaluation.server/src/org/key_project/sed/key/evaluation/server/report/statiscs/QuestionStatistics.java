package org.key_project.sed.key.evaluation.server.report.statiscs;

import java.math.BigInteger;

import org.key_project.sed.key.evaluation.model.definition.AbstractQuestion;
import org.key_project.sed.key.evaluation.model.input.QuestionInput;

/**
 * The statics of an {@link AbstractQuestion}.
 * @author Martin Hentschel
 */
public class QuestionStatistics {
   /**
    * Counts how often the answer was correctly answered.
    */
   private BigInteger correctCount = BigInteger.ZERO;
   
   /**
    * Counts how often the answer was wrongly answered.
    */
   private BigInteger wrongCount = BigInteger.ZERO;
   
   /**
    * Counts how often the trust in the answer was correct.
    */
   private BigInteger correctTrustCount = BigInteger.ZERO;
   
   /**
    * Counts how often the trust in the answer was wrong.
    */
   private BigInteger wrongTrustCount = BigInteger.ZERO;
   
   /**
    * Counts how {@link #timesSum} was updated.
    */
   private BigInteger timesCount = BigInteger.ZERO;
   
   /**
    * The sum of all {@link QuestionInput#getValueSetAt()} values.
    */
   private BigInteger timesSum = BigInteger.ZERO;
   
   /**
    * Counts how {@link #trustTimesSum} was updated.
    */
   private BigInteger trustTimesCount = BigInteger.ZERO;
   
   /**
    * The sum of all {@link QuestionInput#getTrustSetAt()} values.
    */
   private BigInteger trustTimesSum = BigInteger.ZERO;

   /**
    * Default constructor.
    */
   public QuestionStatistics() {
   }
   
   /**
    * Constructor with specified values.
    * @param correctCount The initial value to set.
    * @param wrongCount The initial value to set.
    * @param correctTrustCount The initial value to set.
    * @param wrongTrustCount The initial value to set.
    * @param timesCount The initial value to set.
    * @param timesSum The initial value to set.
    * @param trustTimesCount The initial value to set.
    * @param trustTimesSum The initial value to set.
    */
   public QuestionStatistics(BigInteger correctCount, 
                             BigInteger wrongCount, 
                             BigInteger correctTrustCount, 
                             BigInteger wrongTrustCount, 
                             BigInteger timesCount, 
                             BigInteger timesSum, 
                             BigInteger trustTimesCount, 
                             BigInteger trustTimesSum) {
      this.correctCount = correctCount;
      this.wrongCount = wrongCount;
      this.correctTrustCount = correctTrustCount;
      this.wrongTrustCount = wrongTrustCount;
      this.timesCount = timesCount;
      this.timesSum = timesSum;
      this.trustTimesCount = trustTimesCount;
      this.trustTimesSum = trustTimesSum;
   }

   /**
    * Updates the statics.
    * @param correct
    * @param correctTrust
    * @param time
    * @param trustTime
    */
   protected void update(Boolean correct, Boolean correctTrust, long time, long trustTime) {
      if (correct != null) {
         if (correct) {
            correctCount = correctCount.add(BigInteger.ONE); 
         }
         else {
            wrongCount = wrongCount.add(BigInteger.ONE); 
         }
      }
      if (correctTrust != null) {
         if (correctTrust) {
            correctTrustCount = correctTrustCount.add(BigInteger.ONE); 
         }
         else {
            wrongTrustCount = wrongTrustCount.add(BigInteger.ONE); 
         }
      }
      if (time > 0) {
         timesCount = timesCount.add(BigInteger.ONE); 
         timesSum = timesSum.add(BigInteger.valueOf(time));
      }
      if (trustTime > 0) {
         trustTimesCount = trustTimesCount.add(BigInteger.ONE); 
         trustTimesSum = trustTimesSum.add(BigInteger.valueOf(time));
      }
   }

   /**
    * Returns how often the question was answered wrongly.
    * @return The value.
    */
   public BigInteger getWrongCount() {
      return wrongCount;
   }

   /**
    * Returns how often the trust in the answer was correct.
    * @return The value.
    */
   public BigInteger getCorrectTrustCount() {
      return correctTrustCount;
   }

   /**
    * Returns how often the trust in the answer was wrong.
    * @return The value.
    */
   public BigInteger getWrongTrustCount() {
      return wrongTrustCount;
   }

   /**
    * Returns how often {@link #getTimesSum()} was updated.
    * @return The value.
    */
   public BigInteger getTimesCount() {
      return timesCount;
   }

   /**
    * Returns the sum of all {@link QuestionInput#getValueSetAt()} values.
    * @return The value.
    */
   public BigInteger getTimesSum() {
      return timesSum;
   }

   /**
    * Returns how often {@link #getTrustTimesSum()} was updated.
    * @return The value.
    */
   public BigInteger getTrustTimesCount() {
      return trustTimesCount;
   }

   /**
    * Returns the sum of all {@link QuestionInput#getTrustSetAt()} values.
    * @return The value.
    */
   public BigInteger getTrustTimesSum() {
      return trustTimesSum;
   }

   /**
    * Returns how often the question was answered correctly.
    * @return The value.
    */
   public BigInteger getCorrectCount() {
      return correctCount;
   }
   
   /**
    * Computes the average value time.
    * @return The average value time.
    */
   public BigInteger computeAverageTime() {
      if (!BigInteger.ZERO.equals(timesCount)) {
         return timesSum.divide(timesCount);
      }
      else {
         return BigInteger.ZERO;
      }
   }
   
   /**
    * Computes the average trust time.
    * @return The average trust time.
    */
   public BigInteger computeAverageTrustTime() {
      if (!BigInteger.ZERO.equals(trustTimesCount)) {
         return trustTimesSum.divide(trustTimesCount);
      }
      else {
         return BigInteger.ZERO;
      }
   }
   
   /**
    * Computes how often the answer was correct in average.
    * @return The average correct value.
    */
   public BigInteger computeCorrect() {
      if (!BigInteger.ZERO.equals(correctCount.add(wrongCount))) {
         return correctCount.multiply(BigInteger.valueOf(100)).divide(correctCount.add(wrongCount));
      }
      else {
         return BigInteger.ZERO;
      }
   }
   
   /**
    * Computes how often the trust in the answer was correct in average.
    * @return The average correct value.
    */
   public BigInteger computeTrustCorrect() {
      if (!BigInteger.ZERO.equals(correctTrustCount.add(wrongTrustCount))) {
         return correctTrustCount.multiply(BigInteger.valueOf(100)).divide(correctTrustCount.add(wrongTrustCount));
      }
      else {
         return BigInteger.ZERO;
      }
   }
   
   /**
    * Computes how often the answer was wrong in average.
    * @return The average correct value.
    */
   public BigInteger computeWrong() {
      if (!BigInteger.ZERO.equals(correctCount.add(wrongCount))) {
         return wrongCount.multiply(BigInteger.valueOf(100)).divide(correctCount.add(wrongCount));
      }
      else {
         return BigInteger.ZERO;
      }
   }
   
   /**
    * Computes how often the trust in the answer was wrong in average.
    * @return The average correct value.
    */
   public BigInteger computeTrustWrong() {
      if (!BigInteger.ZERO.equals(correctTrustCount.add(wrongTrustCount))) {
         return wrongTrustCount.multiply(BigInteger.valueOf(100)).divide(correctTrustCount.add(wrongTrustCount));
      }
      else {
         return BigInteger.ZERO;
      }
   }
}