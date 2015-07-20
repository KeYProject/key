package org.key_project.sed.key.evaluation.server.report.statiscs;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;

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
    * The sum of the correctness score.
    */
   private BigInteger scoreSum = BigInteger.ZERO;
   
   /**
    * Counts how often the trust in the answer was correct.
    */
   private BigInteger correctTrustCount = BigInteger.ZERO;
   
   /**
    * Counts how often the trust in the answer was wrong.
    */
   private BigInteger wrongTrustCount = BigInteger.ZERO;
   
   /**
    * The sum of achieved trust points;
    */
   private BigInteger trustScoreSum = BigInteger.ZERO;
   
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
    * @param scoreSum The initial value to set.
    * @param correctTrustCount The initial value to set.
    * @param wrongTrustCount The initial value to set.
    * @param timesCount The initial value to set.
    * @param timesSum The initial value to set.
    * @param trustTimesCount The initial value to set.
    * @param trustTimesSum The initial value to set.
    * @param trustScoreSum The initial value to set.
    */
   public QuestionStatistics(BigInteger correctCount, 
                             BigInteger wrongCount, 
                             BigInteger scoreSum,
                             BigInteger correctTrustCount, 
                             BigInteger wrongTrustCount, 
                             BigInteger timesCount, 
                             BigInteger timesSum, 
                             BigInteger trustTimesCount, 
                             BigInteger trustTimesSum,
                             BigInteger trustScoreSum) {
      this.correctCount = correctCount;
      this.wrongCount = wrongCount;
      this.scoreSum = scoreSum;
      this.correctTrustCount = correctTrustCount;
      this.wrongTrustCount = wrongTrustCount;
      this.timesCount = timesCount;
      this.timesSum = timesSum;
      this.trustTimesCount = trustTimesCount;
      this.trustTimesSum = trustTimesSum;
      this.trustScoreSum = trustScoreSum;
   }

   /**
    * Updates the statics.
    * @param correct
    * @param correctnessScore
    * @param trustScore
    * @param time
    * @param trustTime
    */
   protected void update(Boolean correct, Integer correctnessScore, Integer trustScore, long time, long trustTime) {
      if (correct != null) {
         if (correct) {
            correctCount = correctCount.add(BigInteger.ONE); 
         }
         else {
            wrongCount = wrongCount.add(BigInteger.ONE); 
         }
      }
      if (correctnessScore != null) {
         scoreSum = scoreSum.add(BigInteger.valueOf(correctnessScore.intValue()));
      }
      if (trustScore != null) {
         trustScoreSum = trustScoreSum.add(BigInteger.valueOf(trustScore.intValue()));
         if (trustScore.intValue() > 0) {
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
    * Returns the sum of score.
    * @return The sum of score.
    */
   public BigInteger getScoreSum() {
      return scoreSum;
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
    * Returns the trust score.
    * @return The trust score.
    */
   public BigInteger getTrustScoreSum() {
      return trustScoreSum;
   }

   /**
    * Computes the average trust score.
    * @return The average trust score.
    */
   public BigDecimal computeAverageTrustScore() {
      if (!BigInteger.ZERO.equals(trustScoreSum)) {
         return new BigDecimal(trustScoreSum).divide(new BigDecimal(correctTrustCount.add(wrongTrustCount)), 2, RoundingMode.HALF_EVEN);
      }
      else {
         return BigDecimal.ZERO;
      }
   }

   /**
    * Computes the average correctness score.
    * @return The average correctness score.
    */
   public BigDecimal computeAverageCorrectnessScore() {
      if (!BigInteger.ZERO.equals(correctCount.add(wrongCount))) {
         return new BigDecimal(scoreSum).divide(new BigDecimal(correctCount.add(wrongCount)), 2, RoundingMode.HALF_EVEN);
      }
      else {
         return BigDecimal.ZERO;
      }
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
   public BigDecimal computeCorrect() {
      if (!BigInteger.ZERO.equals(correctCount.add(wrongCount))) {
         return new BigDecimal(correctCount).multiply(BigDecimal.valueOf(100)).divide(new BigDecimal(correctCount.add(wrongCount)), 2, RoundingMode.HALF_EVEN);
      }
      else {
         return BigDecimal.ZERO;
      }
   }
   
   /**
    * Computes how often the trust in the answer was correct in average.
    * @return The average correct value.
    */
   public BigDecimal computeTrustCorrect() {
      if (!BigInteger.ZERO.equals(correctTrustCount.add(wrongTrustCount))) {
         return new BigDecimal(correctTrustCount).multiply(BigDecimal.valueOf(100)).divide(new BigDecimal(correctTrustCount.add(wrongTrustCount)), 2, RoundingMode.HALF_EVEN);
      }
      else {
         return BigDecimal.ZERO;
      }
   }
   
   /**
    * Computes how often the answer was wrong in average.
    * @return The average correct value.
    */
   public BigDecimal computeWrong() {
      if (!BigInteger.ZERO.equals(correctCount.add(wrongCount))) {
         return new BigDecimal(wrongCount).multiply(BigDecimal.valueOf(100)).divide(new BigDecimal(correctCount.add(wrongCount)), 2, RoundingMode.HALF_EVEN);
      }
      else {
         return BigDecimal.ZERO;
      }
   }
   
   /**
    * Computes how often the trust in the answer was wrong in average.
    * @return The average correct value.
    */
   public BigDecimal computeTrustWrong() {
      if (!BigInteger.ZERO.equals(correctTrustCount.add(wrongTrustCount))) {
         return new BigDecimal(wrongTrustCount).multiply(BigDecimal.valueOf(100)).divide(new BigDecimal(correctTrustCount.add(wrongTrustCount)), 2, RoundingMode.HALF_EVEN);
      }
      else {
         return BigDecimal.ZERO;
      }
   }
}