package org.key_project.sed.key.evaluation.server.test.testcase;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.apache.commons.math3.stat.inference.TestUtils;
import org.apache.commons.math3.stat.inference.WilcoxonSignedRankTest;
import org.junit.Test;
import org.key_project.sed.key.evaluation.server.util.StatisticsUtil;

/**
 * Tests for {@link StatisticsUtil}.
 * @author Martin Hentschel
 */
public class StatisticsUtilTest {
   /**
    * Does not test any self implemented functionality, but is used
    * to increase understanding of the Wilcoxon signed rank test offered by {@link WilcoxonSignedRankTest}.
    * <p>
    * The example is taken from 'Experimentation in Software Engineering', Claes Wohlin, Per Runeson, Martin Höst, Magnus C. Ohlsson, Björn Regnell and Anders Wesslén,
    * Table 10.9, page 141.
    */
   @Test
   public void testWilcoxonSignedRankTest_ExperimentationInSoftwareEngineering() {
      double[] firstData = {105, 137, 124, 111, 151, 150, 168, 159, 104, 102};
      double[] secondData = {86.1, 115, 175, 94.9, 174, 120, 153, 178, 71.3, 110};
      WilcoxonSignedRankTest test = new WilcoxonSignedRankTest();
      assertFalse(test.wilcoxonSignedRankTest(firstData, secondData, true) < 0.05);
      assertFalse(test.wilcoxonSignedRankTest(firstData, secondData, false) < 0.05);
   }
   
   /**
    * Does not test any self implemented functionality, but is used
    * to increase understanding of the paired t-Test offered by {@link TestUtils}.
    * <p>
    * The example is taken from 'Experimentation in Software Engineering', Claes Wohlin, Per Runeson, Martin Höst, Magnus C. Ohlsson, Björn Regnell and Anders Wesslén,
    * Table 10.9, page 141.
    */
   @Test
   public void testPairedTTest_ExperimentationInSoftwareEngineering() {
      double[] firstData = {105, 137, 124, 111, 151, 150, 168, 159, 104, 102};
      double[] secondData = {86.1, 115, 175, 94.9, 174, 120, 153, 178, 71.3, 110};
      assertFalse(TestUtils.pairedTTest(firstData, secondData, 0.05));
   }
   
   /**
    * Tests {@link StatisticsUtil#signTest(double[], double[], double, boolean)}
    * with the example from 'Experimentation in Software Engineering', Claes Wohlin, Per Runeson, Martin Höst, Magnus C. Ohlsson, Björn Regnell and Anders Wesslén,
    * Table 10.9, page 141.
    */
   @Test
   public void testSignTestAlpha_ExperimentationInSoftwareEngineering() {
      double[] firstData = {105, 137, 124, 111, 151, 150, 168, 159, 104, 102};
      double[] secondData = {86.1, 115, 175, 94.9, 174, 120, 153, 178, 71.3, 110};
      assertFalse(StatisticsUtil.signTest(firstData, secondData, 0.05, true));
      assertFalse(StatisticsUtil.signTest(firstData, secondData, 0.05, false));
   }
   
   /**
    * Tests {@link StatisticsUtil#signTest(double[], double[])}
    * with the example from 'Experimentation in Software Engineering', Claes Wohlin, Per Runeson, Martin Höst, Magnus C. Ohlsson, Björn Regnell and Anders Wesslén,
    * Table 10.9, page 141.
    */
   @Test
   public void testSignTest_ExperimentationInSoftwareEngineering() {
      double[] firstData = {105, 137, 124, 111, 151, 150, 168, 159, 104, 102};
      double[] secondData = {86.1, 115, 175, 94.9, 174, 120, 153, 178, 71.3, 110};
      assertEquals(0.3770, StatisticsUtil.signTest(firstData, secondData), 0.0001);
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNormalItemsPerSegment(int, int)}.
    */
   @Test
   public void testComputeNormalItemsPerSegment_61_9() {
      int[] normalItemsPerSegment = StatisticsUtil.computeNormalItemsPerSegment(61, 9);
      assertNotNull(normalItemsPerSegment);
      assertEquals(9, normalItemsPerSegment.length);

      assertEquals(6, normalItemsPerSegment[0]);
      assertEquals(7, normalItemsPerSegment[1]);
      assertEquals(7, normalItemsPerSegment[2]);
      assertEquals(7, normalItemsPerSegment[3]);
      assertEquals(7, normalItemsPerSegment[4]);
      assertEquals(7, normalItemsPerSegment[5]);
      assertEquals(7, normalItemsPerSegment[6]);
      assertEquals(7, normalItemsPerSegment[7]);
      assertEquals(6, normalItemsPerSegment[8]);
      int sum = 0;
      for (int value : normalItemsPerSegment) {
         sum += value;
      }
      assertEquals(61, sum);
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNormalItemsPerSegment(int, int)}.
    */
   @Test
   public void testComputeNormalItemsPerSegment_61_8() {
      try {
         StatisticsUtil.computeNormalItemsPerSegment(61, 8);
         fail("Exception expected.");
      }
      catch (IllegalArgumentException e) {
         assertEquals("Can't distribute 61 into 8 segments.", e.getMessage());
      }
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNormalItemsPerSegment(int, int)}.
    */
   @Test
   public void testComputeNormalItemsPerSegment_60_8() {
      int[] normalItemsPerSegment = StatisticsUtil.computeNormalItemsPerSegment(60, 8);
      assertNotNull(normalItemsPerSegment);
      assertEquals(8, normalItemsPerSegment.length);

      assertEquals(7, normalItemsPerSegment[0]);
      assertEquals(7, normalItemsPerSegment[1]);
      assertEquals(8, normalItemsPerSegment[2]);
      assertEquals(8, normalItemsPerSegment[3]);
      assertEquals(8, normalItemsPerSegment[4]);
      assertEquals(8, normalItemsPerSegment[5]);
      assertEquals(7, normalItemsPerSegment[6]);
      assertEquals(7, normalItemsPerSegment[7]);
      int sum = 0;
      for (int value : normalItemsPerSegment) {
         sum += value;
      }
      assertEquals(60, sum);
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNormalItemsPerSegment(int, int)}.
    */
   @Test
   public void testComputeNormalItemsPerSegment_60_10() {
      int[] normalItemsPerSegment = StatisticsUtil.computeNormalItemsPerSegment(60, 10);
      assertNotNull(normalItemsPerSegment);
      assertEquals(10, normalItemsPerSegment.length);
      int sum = 0;
      for (int i = 0; i < normalItemsPerSegment.length; i++) {
         assertEquals(6, normalItemsPerSegment[i]);
         sum += normalItemsPerSegment[i];
      }
      assertEquals(60, sum);
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNumberOfSegments(int)} with
    * an array of length {@code 61}.
    */
   @Test
   public void testComputeNumberOfSegments_61() {
      assertEquals(9, StatisticsUtil.computeNumberOfSegments(61));
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNumberOfSegments(int)} with
    * an array of length {@code 60}.
    */
   @Test
   public void testComputeNumberOfSegments_60() {
      assertEquals(8, StatisticsUtil.computeNumberOfSegments(60));
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNumberOfSegments(int)} with
    * an array of length {@code 40}.
    */
   @Test
   public void testComputeNumberOfSegments_40() {
      assertEquals(7, StatisticsUtil.computeNumberOfSegments(40));
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNumberOfSegments(int)} with
    * an array of length {@code 30}.
    */
   @Test
   public void testComputeNumberOfSegments_30() {
      assertEquals(6, StatisticsUtil.computeNumberOfSegments(30));
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNumberOfSegments(int)} with
    * an array of length {@code 28}.
    */
   @Test
   public void testComputeNumberOfSegments_28() {
      try {
         StatisticsUtil.computeNumberOfSegments(28);
         fail("Exception expected");
      }
      catch (IllegalStateException e) {
         assertEquals("Can't find solution for array of length 28.", e.getMessage());
      }
   }

   /**
    * Tests {@link StatisticsUtil#computeUpperLimitsInNormalDistribution(int, int[])}
    * with the example from 'A Discipline for Software Engineering', Watts S. Humphrey,
    * Table A25, page 541. 
    */
   @Test
   public void testComputeUpperLimitsInNormalDistribution_ADisciplineForSoftwareEngineeringExample() {
      int numberOfItems = 58;
      int[] normalItemsPerSegment = new int[] {5, 6, 6, 6, 6, 6, 6, 6, 6, 5};
      int sum = 0;
      for (int value : normalItemsPerSegment) {
         sum += value;
      }
      assertEquals(numberOfItems, sum);
      double[] limits = StatisticsUtil.computeUpperLimitsInNormalDistribution(numberOfItems, normalItemsPerSegment);
      assertEquals(9, limits.length);
      assertEquals(-1.3663, limits[0], 0.0001);
      assertEquals(-0.8800, limits[1], 0.0001);
      assertEquals(-0.5450, limits[2], 0.0001);
      assertEquals(-0.2626, limits[3], 0.0001);
      assertEquals(0, limits[4], 0.0001);
      assertEquals(0.2626, limits[5], 0.0001);
      assertEquals(0.5450, limits[6], 0.0001);
      assertEquals(0.8800, limits[7], 0.0001);
      assertEquals(1.3663, limits[8], 0.0001);
      for (int i = 0; i < limits.length; i++) {
         if (i >= 1) {
            assertTrue(limits[i] > limits[i - 1]);
         }
      }
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNormalDistributionHistogram(double[], int)}
    * with the example from 'Experimentation in Software Engineering', Claes Wohlin, Per Runeson, Martin Höst, Magnus C. Ohlsson, Björn Regnell and Anders Wesslén,
    * Table 10.20, Table 10.21, page 147.
    */
   @Test
   public void testCreateNormalDistributionHistogram_ExperimentationInSoftwareEngineering() {
      double[] data = {757, 758, 892, 734, 800, 979, 938, 866, 690, 877, 773, 778, 679, 888, 799, 811, 657, 750, 891, 724, 775, 810, 940, 854, 784, 843, 867, 743, 816, 813, 618, 715, 706, 906, 679, 845, 708, 855, 777, 660, 870, 843, 790, 741, 766, 677, 801, 850, 821, 877, 713, 680, 667, 752, 875, 811, 999, 808, 771, 832};
      int numberOfSegments = 10;
      long[] histogram = StatisticsUtil.computeNormalDistributionHistogram(data, numberOfSegments);
      assertNotNull(histogram);
      assertEquals(10, histogram.length);
      assertEquals(8, histogram[0]);
      assertEquals(6, histogram[1]);
      assertEquals(4, histogram[2]);
      assertEquals(6, histogram[3]);
      assertEquals(5, histogram[4]);
      assertEquals(9, histogram[5]);
      assertEquals(2, histogram[6]);
      assertEquals(6, histogram[7]);
      assertEquals(9, histogram[8]);
      assertEquals(5, histogram[9]);
      long sum = 0;
      for (long value : histogram) {
         sum += value;
      }
      assertEquals(data.length, sum);
   }
   
   /**
    * Tests {@link StatisticsUtil#computeNormalDistributionHistogram(double[], int)}
    * with the example from 'A Discipline for Software Engineering', Watts S. Humphrey,
    * Table A22, page 536.
    */
   @Test
   public void testCreateNormalDistributionHistogram_ADisciplineForSoftwareEngineeringExample() {
      double[] data = {5.67, 5.75, 5.80, 6.00, 6.00, 6.00, 7.00, 7.33, 7.50, 7.57, 7.67, 7.80, 8.33, 8.33, 8.67, 8.67, 8.67, 8.83, 9.00, 10.00, 10.33, 10.67, 11.75, 12.00, 13.25, 13.75, 14.00, 14.50, 14.67, 16.40, 16.40, 19.20, 19.33, 20.50, 21.75, 22.25, 24.17, 25.42, 28.33, 29.00, 29.67, 30.14, 36.80, 37.33, 38.00, 39.00, 40.25, 41.00, 50.63, 52.80};
      int numberOfSegments = 10;
      long[] histogram = StatisticsUtil.computeNormalDistributionHistogram(data, numberOfSegments);
      assertNotNull(histogram);
      assertEquals(10, histogram.length);
      assertEquals(0, histogram[0]);
      assertEquals(7, histogram[1]);
      assertEquals(15, histogram[2]);
      assertEquals(7, histogram[3]);
      assertEquals(2, histogram[4]);
      assertEquals(3, histogram[5]);
      assertEquals(3, histogram[6]);
      assertEquals(2, histogram[7]);
      assertEquals(3, histogram[8]);
      assertEquals(8, histogram[9]);
      long sum = 0;
      for (long value : histogram) {
         sum += value;
      }
      assertEquals(data.length, sum);
   }

   /**
    * Tests {@link StatisticsUtil#computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int)}  with a not supported number of segments.
    */
   @Test
   public void testCreateEqualSizedSegmentsUpperLimitsInNormalDistribution_Unsupported() {
      try {
         StatisticsUtil.computeEqualSizedSegmentsUpperLimitsInNormalDistribution(2);
         fail("Exception expected.");
      }
      catch (IllegalArgumentException e) {
         assertEquals("Unsupported number of segments.", e.getMessage());
      }
   }

   /**
    * Tests {@link StatisticsUtil#computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int)} with {@code 12} segments.
    */
   @Test
   public void testCreateEqualSizedSegmentsUpperLimitsInNormalDistribution_12() {
      double[] expected = {-1.383, -0.867, -0.675, -0.431, -0.210, 0.000, 0.210, 0.431, 0.675, 0.867, 1.383};
      doCreateEqualSizedSegmentsUpperLimitsInNormalDistributionTest(12, expected);
   }

   /**
    * Tests {@link StatisticsUtil#computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int)} with {@code 10} segments.
    */
   @Test
   public void testCreateEqualSizedSegmentsUpperLimitsInNormalDistribution_10() {
      double[] expected = {-1.282, -0.842, -0.524, -0.253, 0.000, 0.253, 0.524, 0.842, 1.282};
      doCreateEqualSizedSegmentsUpperLimitsInNormalDistributionTest(10, expected);
   }

   /**
    * Tests {@link StatisticsUtil#computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int)} with {@code 8} segments.
    */
   @Test
   public void testCreateEqualSizedSegmentsUpperLimitsInNormalDistribution_8() {
      double[] expected = {-1.150, -0.675, -0.312, 0.000, 0.312, 0.675, 1.150};
      doCreateEqualSizedSegmentsUpperLimitsInNormalDistributionTest(8, expected);
   }

   /**
    * Tests {@link StatisticsUtil#computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int)} with {@code 7} segments.
    */
   @Test
   public void testCreateEqualSizedSegmentsUpperLimitsInNormalDistribution_7() {
      double[] expected = {-1.067, -0.566, -0.180, 0.180, 0.566, 1.067};
      doCreateEqualSizedSegmentsUpperLimitsInNormalDistributionTest(7, expected);
   }

   /**
    * Tests {@link StatisticsUtil#computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int)} with {@code 6} segments.
    */
   @Test
   public void testCreateEqualSizedSegmentsUpperLimitsInNormalDistribution_6() {
      double[] expected = {-0.967, -0.431, 0.000, 0.431, 0.967};
      doCreateEqualSizedSegmentsUpperLimitsInNormalDistributionTest(6, expected);
   }

   /**
    * Tests {@link StatisticsUtil#computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int)} with {@code 5} segments.
    */
   @Test
   public void testCreateEqualSizedSegmentsUpperLimitsInNormalDistribution_5() {
      double[] expected = {-0.842, -0.253, 0.253, 0.842};
      doCreateEqualSizedSegmentsUpperLimitsInNormalDistributionTest(5, expected);
   }

   /**
    * Tests {@link StatisticsUtil#computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int)} with {@code 4} segments.
    */
   @Test
   public void testCreateEqualSizedSegmentsUpperLimitsInNormalDistribution_4() {
      double[] expected = {-0.766, 0, 0.766};
      doCreateEqualSizedSegmentsUpperLimitsInNormalDistributionTest(4, expected);
   }
   
   /**
    * Performs a {@link StatisticsUtil#computeEqualSizedSegmentsUpperLimitsInNormalDistribution(int)} test.
    * @param numberOfSegments The number of segments.
    * @param expected The expected upper limits.
    */
   protected void doCreateEqualSizedSegmentsUpperLimitsInNormalDistributionTest(int numberOfSegments, double[] expected) {
      double[] current = StatisticsUtil.computeEqualSizedSegmentsUpperLimitsInNormalDistribution(numberOfSegments);
      assertEquals(numberOfSegments - 1, current.length);
      assertEquals(numberOfSegments - 1, expected.length);
      for (int i = 0; i < current.length; i++) {
         assertEquals(expected[i], current[i], 0.0);
         if (i < current.length / 2) {
            assertEquals(current[i] * -1, current[current.length - i - 1], 0.0);
         }
      }
   }
}
