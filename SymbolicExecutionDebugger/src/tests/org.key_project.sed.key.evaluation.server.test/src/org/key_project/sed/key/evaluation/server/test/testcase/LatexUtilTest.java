package org.key_project.sed.key.evaluation.server.test.testcase;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.key_project.sed.key.evaluation.server.util.LatexUtil;

/**
 * Tests for {@link LatexUtil}.
 * @author Martin Hentschel
 */
public class LatexUtilTest {
   /**
    * Tests {@link LatexUtil#medianValue(double[], int)}
    */
   @Test
   public void testMedianValue() {
      assertEquals(1.0, LatexUtil.medianValue(new double[] {1.0}, 0), 0.001);
      assertEquals(1.5, LatexUtil.medianValue(new double[] {1.0, 2.0}, 1), 0.001);
      assertEquals(2.0, LatexUtil.medianValue(new double[] {1.0, 2.0, 3.0}, 1), 0.001);
      assertEquals(2.5, LatexUtil.medianValue(new double[] {1.0, 2.0, 3.0, 4.0}, 2), 0.001);
      assertEquals(3.0, LatexUtil.medianValue(new double[] {1.0, 2.0, 3.0, 4.0, 5.0}, 2), 0.001);
      assertEquals(3.5, LatexUtil.medianValue(new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0}, 3), 0.001);
   }
   
   /**
    * Tests {@link LatexUtil#trunkateDecreasing(int, double[], double)}
    */
   @Test
   public void testTrunkateDecreasing() {
      doTrunkateDecreasingTest(1.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, -4711.0);
      doTrunkateDecreasingTest(1.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 0.0);
      doTrunkateDecreasingTest(1.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 0.5);
      doTrunkateDecreasingTest(1.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 1.0);
      doTrunkateDecreasingTest(2.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 1.5);
      doTrunkateDecreasingTest(2.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.0);
      doTrunkateDecreasingTest(3.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.4);
      doTrunkateDecreasingTest(3.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.5);
      doTrunkateDecreasingTest(3.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.6);
      doTrunkateDecreasingTest(3.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 3.0);
      doTrunkateDecreasingTest(9.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.0);
      doTrunkateDecreasingTest(10.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.4);
      doTrunkateDecreasingTest(10.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.5);
      doTrunkateDecreasingTest(10.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.6);
      doTrunkateDecreasingTest(10.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 10.0);
      doTrunkateDecreasingTest(4711.0, 9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 4711.0);
   }
   
   /**
    * Performs the test steps of {@link #testTrunkateDecreasing()}.
    * @param expectedValue The expected value.
    * @param index The index to start search at.
    * @param array The array to search in.
    * @param reference The reference value to search its nearest occurrence in the array.
    */
   protected void doTrunkateDecreasingTest(double expectedValue, int index, double[] array, double reference) {
      double actualValue = LatexUtil.trunkateDecreasing(index, array, reference);
      assertTrue(actualValue + " >= " + reference + " does not hold.", actualValue >= reference);
      assertEquals(expectedValue, actualValue, 0.001);
   }
   
   /**
    * Tests {@link LatexUtil#trunkateIncreasing(int, double[], double)}
    */
   @Test
   public void testTrunkateIncreasing() {
      doTrunkateIncreasingTest(-4711.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, -4711.0);
      doTrunkateIncreasingTest(0.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 0.0);
      doTrunkateIncreasingTest(0.5, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 0.5);
      doTrunkateIncreasingTest(1.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 1.0);
      doTrunkateIncreasingTest(1.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 1.5);
      doTrunkateIncreasingTest(2.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.0);
      doTrunkateIncreasingTest(2.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.4);
      doTrunkateIncreasingTest(2.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.5);
      doTrunkateIncreasingTest(2.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.6);
      doTrunkateIncreasingTest(3.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 3.0);
      doTrunkateIncreasingTest(9.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.0);
      doTrunkateIncreasingTest(9.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.4);
      doTrunkateIncreasingTest(9.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.5);
      doTrunkateIncreasingTest(9.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.6);
      doTrunkateIncreasingTest(10.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 10.0);
      doTrunkateIncreasingTest(10.0, 0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 4711.0);
   }
   
   /**
    * Performs the test steps of {@link #testTrunkateIncreasing()}.
    * @param expectedValue The expected value.
    * @param index The index to start search at.
    * @param array The array to search in.
    * @param reference The reference value to search its nearest occurrence in the array.
    */
   protected void doTrunkateIncreasingTest(double expectedValue, int index, double[] array, double reference) {
      double actualValue = LatexUtil.trunkateIncreasing(index, array, reference);
      assertTrue(actualValue + " <= " + reference + " does not hold.", actualValue <= reference);
      assertEquals(expectedValue, actualValue, 0.001);
   }
}
