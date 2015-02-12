package org.key_project.util.test.testcase;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.java.NumberUtil;

/**
 * Tests for {@link NumberUtil}.
 * @author Martin Hentschel
 */
public class NumberUtilTest extends TestCase {
   /**
    * Tests {@link NumberUtil#parseFullInt(String)}.
    */
   @Test
   public void testParseFullInt() {
      assertEquals(Integer.MIN_VALUE, NumberUtil.parseFullInt(NumberUtil.toFullString(Integer.MIN_VALUE)));
      assertEquals(-123, NumberUtil.parseFullInt(NumberUtil.toFullString(-123)));
      assertEquals(-12, NumberUtil.parseFullInt(NumberUtil.toFullString(-12)));
      assertEquals(-1, NumberUtil.parseFullInt(NumberUtil.toFullString(-1)));
      assertEquals(0, NumberUtil.parseFullInt(NumberUtil.toFullString(0)));
      assertEquals(1, NumberUtil.parseFullInt(NumberUtil.toFullString(1)));
      assertEquals(12, NumberUtil.parseFullInt(NumberUtil.toFullString(12)));
      assertEquals(123, NumberUtil.parseFullInt(NumberUtil.toFullString(123)));
      assertEquals(Integer.MAX_VALUE, NumberUtil.parseFullInt(NumberUtil.toFullString(Integer.MAX_VALUE)));
      try {
         NumberUtil.parseFullInt(null);
         fail();
      }
      catch (NumberFormatException e) {
         assertEquals("Text not defined.", e.getMessage());
      }
   }
   
   /**
    * Tests {@link NumberUtil#parseFullLong(String)}.
    */
   @Test
   public void testParseFullLong() {
      assertEquals(Long.MIN_VALUE, NumberUtil.parseFullLong(NumberUtil.toFullString(Long.MIN_VALUE)));
      assertEquals(-123, NumberUtil.parseFullLong(NumberUtil.toFullString(-123)));
      assertEquals(-12, NumberUtil.parseFullLong(NumberUtil.toFullString(-12)));
      assertEquals(-1, NumberUtil.parseFullLong(NumberUtil.toFullString(-1)));
      assertEquals(0, NumberUtil.parseFullLong(NumberUtil.toFullString(0)));
      assertEquals(1, NumberUtil.parseFullLong(NumberUtil.toFullString(1)));
      assertEquals(12, NumberUtil.parseFullLong(NumberUtil.toFullString(12)));
      assertEquals(123, NumberUtil.parseFullLong(NumberUtil.toFullString(123)));
      assertEquals(Long.MAX_VALUE, NumberUtil.parseFullLong(NumberUtil.toFullString(Long.MAX_VALUE)));
      try {
         NumberUtil.parseFullInt(null);
         fail();
      }
      catch (NumberFormatException e) {
         assertEquals("Text not defined.", e.getMessage());
      }
   }
   
   /**
    * Tests {@link NumberUtil#toFullString(int)}.
    */
   @Test
   public void testToFullString_int() {
      assertEquals(Integer.toString(Integer.MIN_VALUE), NumberUtil.toFullString(Integer.MIN_VALUE));
      assertEquals("-0000000123", NumberUtil.toFullString(-123));
      assertEquals("-0000000012", NumberUtil.toFullString(-12));
      assertEquals("-0000000001", NumberUtil.toFullString(-1));
      assertEquals("+0000000000", NumberUtil.toFullString(0));
      assertEquals("+0000000001", NumberUtil.toFullString(1));
      assertEquals("+0000000012", NumberUtil.toFullString(12));
      assertEquals("+0000000123", NumberUtil.toFullString(123));
      assertEquals("+" + Integer.MAX_VALUE, NumberUtil.toFullString(Integer.MAX_VALUE));
   }
   
   /**
    * Tests {@link NumberUtil#toFullString(long)}.
    */
   @Test
   public void testToFullString_long() {
      assertEquals(Long.toString(Long.MIN_VALUE), NumberUtil.toFullString(Long.MIN_VALUE));
      assertEquals("-0000000000000000123", NumberUtil.toFullString(-123l));
      assertEquals("-0000000000000000012", NumberUtil.toFullString(-12l));
      assertEquals("-0000000000000000001", NumberUtil.toFullString(-1l));
      assertEquals("+0000000000000000000", NumberUtil.toFullString(0l));
      assertEquals("+0000000000000000001", NumberUtil.toFullString(1l));
      assertEquals("+0000000000000000012", NumberUtil.toFullString(12l));
      assertEquals("+0000000000000000123", NumberUtil.toFullString(123l));
      assertEquals("+" + Long.MAX_VALUE, NumberUtil.toFullString(Long.MAX_VALUE));
   }
   
   /**
    * Tests {@link NumberUtil#getAlgebraicSign(int)}.
    */
   @Test
   public void testGetAlgebraicSign_int() {
      assertEquals('-', NumberUtil.getAlgebraicSign(-10));
      assertEquals('-', NumberUtil.getAlgebraicSign(-1));
      assertEquals('+', NumberUtil.getAlgebraicSign(0));
      assertEquals('+', NumberUtil.getAlgebraicSign(1));
      assertEquals('+', NumberUtil.getAlgebraicSign(10));
   }
   
   /**
    * Tests {@link NumberUtil#getAlgebraicSign(long)}.
    */
   @Test
   public void testGetAlgebraicSign_long() {
      assertEquals('-', NumberUtil.getAlgebraicSign(-10l));
      assertEquals('-', NumberUtil.getAlgebraicSign(-1l));
      assertEquals('+', NumberUtil.getAlgebraicSign(0l));
      assertEquals('+', NumberUtil.getAlgebraicSign(1l));
      assertEquals('+', NumberUtil.getAlgebraicSign(10l));
   }
   
   /**
    * Tests {@link NumberUtil#numberOfDigits(int)}.
    */
   @Test
   public void testNumberOfDigits_int() {
      // Test positive values
      assertEquals(1, NumberUtil.numberOfDigits(0));
      assertEquals(1, NumberUtil.numberOfDigits(1));
      assertEquals(2, NumberUtil.numberOfDigits(10));
      assertEquals(2, NumberUtil.numberOfDigits(11));
      assertEquals(3, NumberUtil.numberOfDigits(100));
      assertEquals(3, NumberUtil.numberOfDigits(111));
      // Test negative values
      assertEquals(1, NumberUtil.numberOfDigits(-0));
      assertEquals(1, NumberUtil.numberOfDigits(-1));
      assertEquals(2, NumberUtil.numberOfDigits(-10));
      assertEquals(2, NumberUtil.numberOfDigits(-11));
      assertEquals(3, NumberUtil.numberOfDigits(-100));
      assertEquals(3, NumberUtil.numberOfDigits(-111));
      // Test max values
      assertEquals(NumberUtil.MAX_INT_DIGITS, NumberUtil.numberOfDigits(Integer.MAX_VALUE));
      assertEquals(NumberUtil.MAX_INT_DIGITS, NumberUtil.numberOfDigits(Integer.MIN_VALUE));
   }
   
   /**
    * Tests {@link NumberUtil#numberOfDigits(long)}.
    */
   @Test
   public void testNumberOfDigits_long() {
      // Test positive values
      assertEquals(1, NumberUtil.numberOfDigits(0l));
      assertEquals(1, NumberUtil.numberOfDigits(1l));
      assertEquals(2, NumberUtil.numberOfDigits(10l));
      assertEquals(2, NumberUtil.numberOfDigits(11l));
      assertEquals(3, NumberUtil.numberOfDigits(100l));
      assertEquals(3, NumberUtil.numberOfDigits(111l));
      // Test negative values
      assertEquals(1, NumberUtil.numberOfDigits(-0l));
      assertEquals(1, NumberUtil.numberOfDigits(-1l));
      assertEquals(2, NumberUtil.numberOfDigits(-10l));
      assertEquals(2, NumberUtil.numberOfDigits(-11l));
      assertEquals(3, NumberUtil.numberOfDigits(-100l));
      assertEquals(3, NumberUtil.numberOfDigits(-111l));
      // Test max values
      assertEquals(NumberUtil.MAX_LONG_DIGITS, NumberUtil.numberOfDigits(Long.MAX_VALUE));
      assertEquals(NumberUtil.MAX_LONG_DIGITS, NumberUtil.numberOfDigits(Long.MIN_VALUE));
   }
}
