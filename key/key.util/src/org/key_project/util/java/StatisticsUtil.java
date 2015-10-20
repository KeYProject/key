package org.key_project.util.java;

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
    * Computes a histogram according to the normal distribution as described
    * by 'A Discipline for Software Engineering', Watts S. Humphrey,
    * Table A21 (step 8), page 534.
    * @param data The actual data.
    * @param numberOfSegments The number of segments.
    * @return The created histogram according to the normal distribution.
    */
   public static long[] createNormalDistributionHistogram(double[] data, int numberOfSegments) {
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
      double[] upperLimits = createEqualSizedSegmentsUpperLimitsInNormalDistribution(numberOfSegments);
      // Create histogram
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
   public static double[] createEqualSizedSegmentsUpperLimitsInNormalDistribution(int numberOfSegments) throws IllegalArgumentException {
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
}
