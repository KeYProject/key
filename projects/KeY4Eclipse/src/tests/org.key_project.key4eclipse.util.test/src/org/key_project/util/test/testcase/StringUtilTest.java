/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

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
    * Tests {@link StringUtil#equalIgnoreWhiteSpace(String, String)}.
    */
   @Test
   public void testEqualIgnoreWhiteSpace() {
      assertTrue(StringUtil.equalIgnoreWhiteSpace(null, null));
      assertFalse(StringUtil.equalIgnoreWhiteSpace("A", null));
      assertFalse(StringUtil.equalIgnoreWhiteSpace("B", null));
      assertTrue(StringUtil.equalIgnoreWhiteSpace("A", "A"));
      assertTrue(StringUtil.equalIgnoreWhiteSpace("A B", "A B"));
      assertTrue(StringUtil.equalIgnoreWhiteSpace("A B C", "A B C"));
      assertTrue(StringUtil.equalIgnoreWhiteSpace("A    B    C", "A\nB\r\tC"));
      assertFalse(StringUtil.equalIgnoreWhiteSpace("A B C", "A B C D"));
      assertFalse(StringUtil.equalIgnoreWhiteSpace("A B C D", "A B C"));
      assertTrue(StringUtil.equalIgnoreWhiteSpace("  A B C", "A B C\t\n"));
   }
   
   /**
    * Tests {@link StringUtil#toSingleLinedString(String)}
    */
   @Test
   public void testToSingleLinedString() {
      String text = "First Line\nSecond Line\nLine\twith\tTabs\nLast Line";
      assertNull(StringUtil.toSingleLinedString(null));
      assertEquals("", StringUtil.toSingleLinedString(""));
      assertEquals("First Line Second Line Line with Tabs Last Line", StringUtil.toSingleLinedString(text));
   }
   
   /**
    * Tests {@link StringUtil#replaceAll(String, char[], char)}
    */
   @Test
   public void testReplaceAll() {
      String text = "ABCDABCDABCDABCD";
      assertNull(StringUtil.replaceAll(null, new char[] {}, 'X'));
      assertEquals(text, StringUtil.replaceAll(text, null, 'X'));
      assertEquals(text, StringUtil.replaceAll(text, new char[] {}, 'X'));
      assertEquals("XBCDXBCDXBCDXBCD", StringUtil.replaceAll(text, new char[] {'A'}, 'X'));
      assertEquals("AXCDAXCDAXCDAXCD", StringUtil.replaceAll(text, new char[] {'B'}, 'X'));
      assertEquals("ABXDABXDABXDABXD", StringUtil.replaceAll(text, new char[] {'C'}, 'X'));
      assertEquals("ABCXABCXABCXABCX", StringUtil.replaceAll(text, new char[] {'D'}, 'X'));
      assertEquals("ABCDABCDABCDABCD", StringUtil.replaceAll(text, new char[] {'E'}, 'X'));
      assertEquals("XBXDXBXDXBXDXBXD", StringUtil.replaceAll(text, new char[] {'A', 'C'}, 'X'));
      assertEquals("XXXXXXXXXXXXXXXX", StringUtil.replaceAll(text, new char[] {'A', 'B', 'C', 'D'}, 'X'));
   }
   
   /**
    * Tests {@link StringUtil#contains(String, CharSequence)}
    */
   @Test
   public void testContains() {
      assertFalse(StringUtil.contains(null, "A"));
      assertFalse(StringUtil.contains("A", null));
      assertFalse(StringUtil.contains("A", "B"));
      assertTrue(StringUtil.contains("A", "A"));
      assertTrue(StringUtil.contains("A", ""));
      assertFalse(StringUtil.contains("", "A"));
      assertTrue(StringUtil.contains("Hello", "He"));
      assertTrue(StringUtil.contains("Hello", "ell"));
      assertTrue(StringUtil.contains("Hello", "ello"));
   }
   
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