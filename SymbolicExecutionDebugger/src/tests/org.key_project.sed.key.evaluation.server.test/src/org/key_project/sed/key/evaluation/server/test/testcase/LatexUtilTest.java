package org.key_project.sed.key.evaluation.server.test.testcase;

import static org.junit.Assert.assertEquals;

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
      assertEquals(1.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, -4711.0), 0.001);
      assertEquals(1.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 0.0), 0.001);
      assertEquals(1.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 0.5), 0.001);
      assertEquals(1.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 1.0), 0.001);
      assertEquals(2.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 1.5), 0.001);
      assertEquals(2.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.0), 0.001);
      assertEquals(2.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.4), 0.001);
      assertEquals(3.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.5), 0.001);
      assertEquals(3.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.6), 0.001);
      assertEquals(3.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 3.0), 0.001);
      assertEquals(9.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.0), 0.001);
      assertEquals(9.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.4), 0.001);
      assertEquals(10.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.5), 0.001);
      assertEquals(10.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.6), 0.001);
      assertEquals(10.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 10.0), 0.001);
      assertEquals(10.0, LatexUtil.trunkateDecreasing(9, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 4711.0), 0.001);
   }
   
   /**
    * Tests {@link LatexUtil#trunkateIncreasing(int, double[], double)}
    */
   @Test
   public void testTrunkateIncreasing() {
      assertEquals(1.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, -4711.0), 0.001);
      assertEquals(1.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 0.0), 0.001);
      assertEquals(1.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 0.5), 0.001);
      assertEquals(1.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 1.0), 0.001);
      assertEquals(1.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 1.5), 0.001);
      assertEquals(2.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.0), 0.001);
      assertEquals(2.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.4), 0.001);
      assertEquals(2.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.5), 0.001);
      assertEquals(3.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 2.6), 0.001);
      assertEquals(3.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 3.0), 0.001);
      assertEquals(9.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.0), 0.001);
      assertEquals(9.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.4), 0.001);
      assertEquals(9.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.5), 0.001);
      assertEquals(10.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 9.6), 0.001);
      assertEquals(10.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 10.0), 0.001);
      assertEquals(10.0, LatexUtil.trunkateIncreasing(0, new double[] {1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0}, 4711.0), 0.001);
   }
}
