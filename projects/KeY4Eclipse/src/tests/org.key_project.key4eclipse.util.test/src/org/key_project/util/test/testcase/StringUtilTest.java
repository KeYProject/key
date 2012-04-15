package org.key_project.util.test.testcase;

import java.util.Comparator;

import junit.framework.TestCase;

import org.junit.Test;
import org.key_project.util.java.StringUtil;

/**
 * Tests for {@link StringUtil}
 * @author Martin Hentschel
 */
public class StringUtilTest extends TestCase {
   /**
    * Tests {@link StringUtil#createLine(String, int)}
    */
   @Test
   public void testCreateLine() {
      // Test line with one character
      assertEquals("", StringUtil.createLine("#", -1));
      assertEquals("", StringUtil.createLine("#", 0));
      assertEquals("-", StringUtil.createLine("-", 1));
      assertEquals("AA", StringUtil.createLine("A", 2));
      assertEquals("#####", StringUtil.createLine("#", 5));
      // Test line with multiple characters
      assertEquals("ABABAB", StringUtil.createLine("AB", 3));
      // Test null text
      assertEquals("nullnullnullnull", StringUtil.createLine(null, 4));
   }
   
   /**
    * Tests {@link StringUtil#createIgnoreCaseComparator()}.
    */
   @Test
   public void testCreateIgnoreCaseComparator() {
      Comparator<String> c = StringUtil.createIgnoreCaseComparator();
      assertNotNull(c);
      assertSame("A".compareToIgnoreCase("A"), c.compare("A", "A"));
      assertSame("A".compareToIgnoreCase("a"), c.compare("A", "a"));
      assertSame("A".compareToIgnoreCase("B"), c.compare("A", "B"));
      assertSame("A".compareToIgnoreCase("b"), c.compare("A", "b"));
      assertSame("a".compareToIgnoreCase("B"), c.compare("a", "B"));
      assertSame("A".compareToIgnoreCase("B"), c.compare("A", "B"));
      assertNotSame(0, c.compare("A", null));
      assertNotSame(0, c.compare(null, "A"));
      assertSame(0, c.compare(null, null));
   }
    
   /**
    * Tests {@link StringUtil#toLowerCase(String)}
    */
   @Test
   public void testToLowerCase() {
       assertNull(StringUtil.toLowerCase(null));
       assertEquals("aa", StringUtil.toLowerCase("AA"));
       assertEquals("aa", StringUtil.toLowerCase("aa"));
       assertEquals("aa", StringUtil.toLowerCase("Aa"));
       assertEquals("aa", StringUtil.toLowerCase("aA"));
   }

   /**
    * Tests {@link StringUtil#trim(String)}
    */
   @Test
   public void testTrim() {
      assertNull(StringUtil.trim(null));
      assertEquals("AA", StringUtil.trim("AA"));
      assertEquals("AA", StringUtil.trim(" AA "));
   }
   
   /**
    * Tests {@link StringUtil#isTrimmedEmpty(String)}
    */
   @Test
   public void testIsTrimmedEmpty() {
      assertTrue(StringUtil.isTrimmedEmpty(null));
      assertTrue(StringUtil.isTrimmedEmpty(""));
      assertTrue(StringUtil.isTrimmedEmpty(" "));
      assertFalse(StringUtil.isTrimmedEmpty(" A "));
   }

   /**
    * Tests {@link StringUtil#isEmpty(String)}
    */
   @Test
   public void testIsEmpty() {
      assertTrue(StringUtil.isEmpty(null));
      assertTrue(StringUtil.isEmpty(""));
      assertFalse(StringUtil.isEmpty(" "));
      assertFalse(StringUtil.isEmpty(" A "));
   }
}
