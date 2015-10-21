package org.key_project.sed.key.evaluation.server.util;

import org.apache.commons.math3.util.CombinatoricsUtils;

/**
 * Provides utility methods for statistics, e.g. in combination with
 * <a href="https://commons.apache.org/proper/commons-math/">The Apache Commons Mathematics Library</a>.
 * @author Martin Hentschel
 */
public final class StatisticsUtil {
   /**
    * Forbid instances.
    */
   private StatisticsUtil() {
   }
   
   /**
    * Tests the p-value of a sign test against a given alpha according to
    * 'Experimentation in Software Engineering', Claes Wohlin, Per Runeson, Martin Höst, Magnus C. Ohlsson, Björn Regnell and Anders Wesslén,
    * Table 10.11, page 142.
    * <p>
    * H0: P(+) = P(-) where + and - represent the two events that firstData_i > secondData_i and firstData_i < secondData_i
    * <ul>
    *    <li>Two Sided: (H1 : P(+) != P(-)): reject H0 if p < alpha/2</li>
    *    <li>One Sided: (H1 : P(+) < P(-)): reject H0 if p < alpha and the + event is the most rare event in the sample</li>
    * </ul>
    * @param firstData The first data.
    * @param secondData The second data.
    * @param alpha The fixed alpha.
    * @param twoSided {@code true} two sided test, {@code false} one side test.
    * @return {@code true} if null hypothesis H0 is rejected at the alpha level, {@code false} otherwise.
    * @throws IllegalArgumentException if the parameters are invalid.
    */
   public static boolean signTest(double[] firstData, double[] secondData, double alpha, boolean twoSided) throws IllegalArgumentException {
      SignTestResult result = doSignTest(firstData, secondData);
      if (twoSided) {
         return result.p < (alpha / 2);
      }
      else {
         return result.p < alpha && result.pPlusCount < result.pMinusCount;
      }
   }
   
   /**
    * Computes the p-value of a sign test according to
    * 'Experimentation in Software Engineering', Claes Wohlin, Per Runeson, Martin Höst, Magnus C. Ohlsson, Björn Regnell and Anders Wesslén,
    * Table 10.11, page 142.
    * <p>
    * H0: P(+) = P(-) where + and - represent the two events that firstData_i > secondData_i and firstData_i < secondData_i
    * @param firstData The first data.
    * @param secondData The second data.
    * @return The computed p-value.
    * @throws IllegalArgumentException if the parameters are invalid.
    */
   public static double signTest(double[] firstData, double[] secondData) throws IllegalArgumentException {
      return doSignTest(firstData, secondData).p;
   }
   
   /**
    * Utility method of {@link #signTest(double[], double[])} and
    * {@link #signTest(double[], double[], double, boolean)}.
    * @param firstData The first data.
    * @param secondData The second data.
    * @return The result.
    * @throws IllegalArgumentException if the parameters are invalid.
    */
   private static SignTestResult doSignTest(double[] firstData, double[] secondData) throws IllegalArgumentException {
      if (firstData.length != secondData.length) {
         throw new IllegalArgumentException("First and second data have different lenght.");
      }
      int pPlusCount = 0;
      int pMinusCount = 0;
      for (int i = 0; i < firstData.length; i++) {
         if (firstData[i] > secondData[i]) {
            pPlusCount++;
         }
         else if (firstData[i] < secondData[i]) {
            pMinusCount++;
         }
      }
      int n = Math.min(pPlusCount, pMinusCount);
      int N = pPlusCount + pMinusCount;
      double tempSum = 0.0;
      for (int i = 0; i <= n; i++) {
         tempSum += CombinatoricsUtils.binomialCoefficientDouble(N, i);
      }
      double p = 1.0 / Math.pow(2.0, N) * tempSum;
      return new SignTestResult(p, pPlusCount, pMinusCount);
   }
   
   /**
    * Helper class instantiated by {@link StatisticsUtil#doSignTest(double[], double[])}.
    * @author Martin Hentschel
    */
   private final static class SignTestResult {
      /**
       * The p-value.
       */
      private final double p;
      
      /**
       * The P(+) count.
       */
      private final int pPlusCount;
      
      /**
       * The P(-) count.
       */
      private final int pMinusCount;

      /**
       * Constructor.
       * @param p The p-value.
       * @param pPlusCount The P(+) count.
       * @param pMinusCount The P(-) count.
       */
      public SignTestResult(double p, int pPlusCount, int pMinusCount) {
         this.p = p;
         this.pPlusCount = pPlusCount;
         this.pMinusCount = pMinusCount;
      }
   }
   
   /**
    * Computes a histogram according to the normal distribution as described
    * by 'A Discipline for Software Engineering', Watts S. Humphrey,
    * Table A21 (step 8), page 534.
    * @param data The actual data.
    * @return The created histogram according to the normal distribution.
    * @throws IllegalArgumentException if no histogram could be computed.
    */
   public static long[] computeNormalDistributionHistogram(double[] data) throws IllegalArgumentException {
      int numberOfSegments = computeNumberOfSegments(data.length);
      int[] normalItemsPerSegment = computeNormalItemsPerSegment(data.length, numberOfSegments);
      double[] upperLimits = computeUpperLimitsInNormalDistribution(data.length, normalItemsPerSegment);
      return computeNormalDistributionHistogram(data, upperLimits);
   }

   /**
    * Distributes the number of data items into the given number of segments.
    * @param numberOfDataItems The number of data items.
    * @param numberOfSegments The number of segments
    * @return The created normal items distribution.
    * @throws IllegalArgumentException if a distribution is not possible.
    */
   public static int[] computeNormalItemsPerSegment(int numberOfDataItems, int numberOfSegments) throws IllegalArgumentException {
      int[] normalItemsPerSegment = new int[numberOfSegments];
      // Distribute equal amount
      for (int i = 0; i < normalItemsPerSegment.length; i++) {
         normalItemsPerSegment[i] = numberOfDataItems / numberOfSegments;
      }
      // Distribute unequal amount
      int remaining = numberOfDataItems % numberOfSegments;
      int offset = (numberOfSegments - remaining) / 2;
      if ((numberOfSegments - remaining) % 2 != 0) {
         throw new IllegalArgumentException("Can't distribute " + numberOfDataItems + " into " + numberOfSegments + " segments.");
      }
      for (int i = offset; i < offset + remaining; i++) {
         normalItemsPerSegment[i]++;
      }
      return normalItemsPerSegment;
   }
   
   /**
    * Computes the number of segments in a histogram according to the normal distribution.
    * @param numberOfDataItems The number of data items.
    * @return The number of segments in the histogram according to the normal distribution.
    * @throws IllegalArgumentException if no solution was found.
    */
   public static int computeNumberOfSegments(int numberOfDataItems) throws IllegalArgumentException {
      int candidate = (int) Math.ceil(Math.sqrt((double) numberOfDataItems));
      // Find valid candidate
      while ((!testNumberOfSegmentsCandidate(numberOfDataItems, candidate) 
              || (candidate - (numberOfDataItems % candidate)) % 2 != 0 /* Ensures that data items can be distributed according to normal distribution. */) 
             && candidate <= numberOfDataItems 
             && numberOfDataItems / candidate >= 5) {
         candidate++;
      }
      if (testNumberOfSegmentsCandidate(numberOfDataItems, candidate)) {
         return candidate;
      }
      else {
         throw new IllegalStateException("Can't find solution for array of length " + numberOfDataItems + ".");
      }
   }

   /**
    * Utility method of {@link #computeNumberOfSegments(double[])} to
    * test a given candidate.
    * @param numberOfDataItems The number of data items.
    * @param candidate The candidate to test.
    * @return {@code true} candidate is valid, {@code false} candidate is not valid.
    */
   private static boolean testNumberOfSegmentsCandidate(int numberOfDataItems, int candidate) {
      return (numberOfDataItems / candidate >= 5) &&
             (candidate > 3) &&
             (candidate * candidate >= numberOfDataItems);
   }
      
   /**
    * Computes a histogram according to the normal distribution as described
    * by 'A Discipline for Software Engineering', Watts S. Humphrey,
    * Table A21 (step 8), page 534.
    * @param data The actual data.
    * @param numberOfSegments The number of segments.
    * @return The created histogram according to the normal distribution.
    * @throws IllegalArgumentException if the parameters are invalid.
    */
   public static long[] computeNormalDistributionHistogram(double[] data, int numberOfSegments) throws IllegalArgumentException {
      // Test parameter
      if (!(data.length / numberOfSegments >= 5)) {
         throw new IllegalArgumentException("data.length / numberOfSegments >= 5 does not hold.");
      }
      if (!(numberOfSegments > 3)) {
         throw new IllegalArgumentException("numberOfSegments > 3 does not hold.");
      }
      if (!(numberOfSegments * numberOfSegments >= data.length)) {
         throw new IllegalArgumentException("numberOfSegments * numberOfSegments >= data.length does not hold.");
      }
      if (!(data.length % numberOfSegments == 0)) {
         throw new IllegalArgumentException("Groups of different size are currently not supported.");
      }
      // Compute upper limits
      double[] upperLimits = computeEqualSizedSegmentsUpperLimitsInNormalDistribution(numberOfSegments);
      // Compute histogram
      return computeNormalDistributionHistogram(data, upperLimits);
   }
   
   /**
    * Computes a histogram according to the normal distribution as described
    * by 'A Discipline for Software Engineering', Watts S. Humphrey,
    * Table A21 (step 8), page 534.
    * @param data The actual data.
    * @param numberOfSegments The number of segments.
    * @return The created histogram according to the normal distribution.
    */
   public static long[] computeNormalDistributionHistogram(double[] data, double[] upperLimits) {
      // Compute parameters (avg and standard deviation)
      double sum = 0.0;
      for (double value : data) {
         sum += value;
      }
      double avg = sum / data.length;
      double varianceSum = 0.0;
      for (double value : data) {
         varianceSum += (value - avg) * (value - avg);
      }
      double variance = (1.0 / (data.length - 1)) * varianceSum;
      double standardDeviation = Math.sqrt(variance);
      // Get upper limits
      // Create histogram
      int numberOfSegments = upperLimits.length + 1;
      long[] histogram = new long[numberOfSegments];
      for (double value : data) {
         double normalForm = (value - avg) / standardDeviation;
         // Search limit
         int i = 0;
         boolean found = false;
         while (!found && i < upperLimits.length) {
            if (normalForm <= upperLimits[i]) {
               found = true;
            }
            else {
               i++;
            }
         }
         if (found) {
            histogram[i]++;
         }
         else {
            histogram[histogram.length - 1]++;
         }
      }
      return histogram;
   }
   
   /**
    * Creates an array with the upper bounds of the normal distribution segments
    * according to 'A Discipline for Software Engineering', Watts S. Humphrey,
    * Table A24, page 539.
    * @param numberOfSegments The values {@code 4}, {@code 5}, {@code 6}, {@code 7}, {@code 8}, {@code 10} and {@code 12} are supported. 
    * @return The created array with the upper bounds. The missing last segment has no upper bound.
    * @throws IllegalArgumentException if the {@code numberOfSegments} is not supported.
    */
   public static double[] computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int numberOfSegments) throws IllegalArgumentException {
      if (numberOfSegments == 4) {
         return new double[] {-0.766, 0, 0.766};
      }
      else if (numberOfSegments == 5) {
         return new double[] {-0.842, -0.253, 0.253, 0.842};
      }
      else if (numberOfSegments == 6) {
         return new double[] {-0.967, -0.431, 0, 0.431, 0.967};
      }
      else if (numberOfSegments == 7) {
         return new double[] {-1.067, -0.566, -0.180, 0.180, 0.566, 1.067};
      }
      else if (numberOfSegments == 8) {
         return new double[] {-1.150, -0.675, -0.312, 0.000, 0.312, 0.675, 1.150};
      }
      else if (numberOfSegments == 10) {
         return new double[] {-1.282, -0.842, -0.524, -0.253, 0.000, 0.253, 0.524, 0.842, 1.282};
      }
      else if (numberOfSegments == 12) {
         return new double[] {-1.383, -0.867, -0.675, -0.431, -0.210, 0.000, 0.210, 0.431, 0.675, 0.867, 1.383};
      }
      else {
         throw new IllegalArgumentException("Unsupported number of segments.");
      }
   }

   /**
    * Creates an array with the upper bounds of the normal distribution segments
    * according to 'A Discipline for Software Engineering', Watts S. Humphrey,
    * Example of a ChiSquare Test with Unequal Segments, page 540.
    * @param numberOfDataItems The number of data items.
    * @param normalItemsPerSegment The number of normal items per segment.
    * @return The created array with the upper bounds. The missing last segment has no upper bound.
    */
   public static double[] computeUpperLimitsInNormalDistribution(int numberOfDataItems, int[] normalItemsPerSegment) {
      double partRange = 1.0 / numberOfDataItems;
      double[] cumulativeSegmentArea = new double[normalItemsPerSegment.length];
      for (int i = 0; i < normalItemsPerSegment.length; i++) {
         cumulativeSegmentArea[i] = normalItemsPerSegment[i] * partRange;
         if (i >= 1) {
            cumulativeSegmentArea[i] += cumulativeSegmentArea[i - 1];
         }
      }
      double[] upperLimits = new double[normalItemsPerSegment.length - 1];
      NormalDistributionPair[] nd = createSelectedValuesOfTheStandardNormalDistribution();
      if (nd.length < normalItemsPerSegment.length) {
         throw new IllegalStateException("Not enough granularity in the normal distribution table.");
      }
      for (int i = 0; i < cumulativeSegmentArea.length - 1; i++) {
         int ndIndex = 0;
         boolean found = false;
         while (!found && ndIndex < nd.length) {
            if (cumulativeSegmentArea[i] <= nd[ndIndex].getP()) {
               found = true;
            }
            else {
               ndIndex++;
            }
         }
         assert found : "Normal distribution item not found.";
         if (cumulativeSegmentArea[i] == nd[ndIndex].getP()) {
            upperLimits[i] = nd[ndIndex].getP();
         }
         else {
            NormalDistributionPair below = nd[ndIndex - 1];
            NormalDistributionPair above = nd[ndIndex];
            upperLimits[i] = below.getX() + ((cumulativeSegmentArea[i] - below.getP()) / (above.getP() - below.getP())) * (above.getX() - below.getX());
         }
      }
      return upperLimits;
   }
   
   /**
    * Returns selected values of the Standard Normal Distribution according to
    * 'A Discipline for Software Engineering', Watts S. Humphrey, Table A1, page 488.
    * @return The sorted values of the Standard Normal Distribution.
    */
   public static NormalDistributionPair[] createSelectedValuesOfTheStandardNormalDistribution() {
      return new NormalDistributionPair[] {  
         new NormalDistributionPair(-4.0, 0.0000),
         new NormalDistributionPair(-3.9, 0.0000),
         new NormalDistributionPair(-3.8, 0.0001),
         new NormalDistributionPair(-3.7, 0.0001),
         new NormalDistributionPair(-3.6, 0.0002),
         new NormalDistributionPair(-3.5, 0.0002),
         new NormalDistributionPair(-3.4, 0.0003),
         new NormalDistributionPair(-3.3, 0.0005),
         new NormalDistributionPair(-3.2, 0.0007),
         new NormalDistributionPair(-3.1, 0.0010),
         new NormalDistributionPair(-3.0, 0.0013),
         new NormalDistributionPair(-2.9, 0.0019),
         new NormalDistributionPair(-2.8, 0.0026),
         new NormalDistributionPair(-2.7, 0.0035),
         new NormalDistributionPair(-2.6, 0.0047),
         new NormalDistributionPair(-2.5, 0.0062),
         new NormalDistributionPair(-2.4, 0.0082),
         new NormalDistributionPair(-2.3, 0.0107),
         new NormalDistributionPair(-2.2, 0.0139),
         new NormalDistributionPair(-2.1, 0.0179),
         new NormalDistributionPair(-2.0, 0.0227),
         new NormalDistributionPair(-1.9, 0.0287),
         new NormalDistributionPair(-1.8, 0.0359),
         new NormalDistributionPair(-1.7, 0.0446),
         new NormalDistributionPair(-1.6, 0.0548),
         new NormalDistributionPair(-1.5, 0.0668),
         new NormalDistributionPair(-1.4, 0.0808),
         new NormalDistributionPair(-1.3, 0.0968),
         new NormalDistributionPair(-1.2, 0.1151),
         new NormalDistributionPair(-1.1, 0.1357),
         new NormalDistributionPair(-1.0, 0.1587),
         new NormalDistributionPair(-0.9, 0.1841),
         new NormalDistributionPair(-0.8, 0.2119),
         new NormalDistributionPair(-0.7, 0.2420),
         new NormalDistributionPair(-0.6, 0.2743),
         new NormalDistributionPair(-0.5, 0.3085),
         new NormalDistributionPair(-0.4, 0.3446),
         new NormalDistributionPair(-0.3, 0.3821),
         new NormalDistributionPair(-0.2, 0.4207),
         new NormalDistributionPair(-0.1, 0.4602),
         new NormalDistributionPair(0.0, 0.5000),
         new NormalDistributionPair(0.1, 0.5398),
         new NormalDistributionPair(0.2, 0.5793),
         new NormalDistributionPair(0.3, 0.6179),
         new NormalDistributionPair(0.4, 0.6554),
         new NormalDistributionPair(0.5, 0.6915),
         new NormalDistributionPair(0.6, 0.7257),
         new NormalDistributionPair(0.7, 0.7580),
         new NormalDistributionPair(0.8, 0.7881),
         new NormalDistributionPair(0.9, 0.8159),
         new NormalDistributionPair(1.0, 0.8413),
         new NormalDistributionPair(1.1, 0.8643),
         new NormalDistributionPair(1.2, 0.8849),
         new NormalDistributionPair(1.3, 0.9032),
         new NormalDistributionPair(1.4, 0.9192),
         new NormalDistributionPair(1.5, 0.9332),
         new NormalDistributionPair(1.6, 0.9452),
         new NormalDistributionPair(1.7, 0.9554),
         new NormalDistributionPair(1.8, 0.9641),
         new NormalDistributionPair(1.9, 0.9713),
         new NormalDistributionPair(2.0, 0.9773),
         new NormalDistributionPair(2.1, 0.9821),
         new NormalDistributionPair(2.2, 0.9861),
         new NormalDistributionPair(2.3, 0.9893),
         new NormalDistributionPair(2.4, 0.9918),
         new NormalDistributionPair(2.5, 0.9938),
         new NormalDistributionPair(2.6, 0.9953),
         new NormalDistributionPair(2.7, 0.9965),
         new NormalDistributionPair(2.8, 0.9974),
         new NormalDistributionPair(2.9, 0.9981),
         new NormalDistributionPair(3.0, 0.9987),
         new NormalDistributionPair(3.1, 0.9990),
         new NormalDistributionPair(3.2, 0.9993),
         new NormalDistributionPair(3.3, 0.9995),
         new NormalDistributionPair(3.4, 0.9997),
         new NormalDistributionPair(3.5, 0.9998),
         new NormalDistributionPair(3.6, 0.9998),
         new NormalDistributionPair(3.7, 0.9999),
         new NormalDistributionPair(3.8, 0.9999),
         new NormalDistributionPair(3.9, 1.0000),
         new NormalDistributionPair(4.0, 1.0000)
      };
   }
   
   /**
    * An entry in the standard normal distribution created by
    * {@link StatisticsUtil#createSelectedValuesOfTheStandardNormalDistribution()}.
    * @author Martin Hentschel
    */
   public static final class NormalDistributionPair {
      /**
       * The x-value.
       */
      private final double x;
      
      /**
       * The p-value.
       */
      private final double p;
      
      /**
       * Constructor.
       * @param x The x-value.
       * @param p The p-value.
       */
      private NormalDistributionPair(double x, double p) {
         this.x = x;
         this.p = p;
      }
      
      /**
       * Returns the x-value.
       * @return The x-value.
       */
      public double getX() {
         return x;
      }
      
      /**
       * Returns the p-value.
       * @return The p-value.
       */
      public double getP() {
         return p;
      }
   }
}
