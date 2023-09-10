/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.testcase.java;

import java.util.Comparator;

import org.key_project.util.java.StringUtil;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;
import static org.key_project.util.java.StringUtil.count;
import static org.key_project.util.java.StringUtil.trim;

/**
 * Tests for {@link StringUtil}
 *
 * @author Martin Hentschel
 */
public class StringUtilTest {
    /**
     * Tests {@link StringUtil#startsWith(Object, String)}
     */
    @Test
    public void testStartsWith() {
        assertTrue(StringUtil.startsWith("Hello", "Hello"));
        assertTrue(StringUtil.startsWith("Hello", "Hell"));
        assertTrue(StringUtil.startsWith("Hello", "Hel"));
        assertTrue(StringUtil.startsWith("Hello", "He"));
        assertTrue(StringUtil.startsWith("Hello", "H"));
        assertTrue(StringUtil.startsWith("Hello", ""));
        assertFalse(StringUtil.startsWith("Hello", null));
        assertFalse(StringUtil.startsWith(null, ""));
        assertFalse(StringUtil.startsWith(null, "H"));
        assertFalse(StringUtil.startsWith(new Object() {
            @Override
            public String toString() {
                return "Hello";
            }
        }, "H"));
    }

    /**
     * Tests {@link StringUtil#chop(String, int)}
     */
    @Test
    public void testChop() {
        assertNull(StringUtil.chop(null, 0));
        assertNull(StringUtil.chop(null, 10));
        assertEquals("", StringUtil.chop("1234567890", -1));
        assertEquals("", StringUtil.chop("1234567890", 0));
        assertEquals(".", StringUtil.chop("1234567890", 1));
        assertEquals("..", StringUtil.chop("1234567890", 2));
        assertEquals("...", StringUtil.chop("1234567890", 3));
        assertEquals("1...", StringUtil.chop("1234567890", 4));
        assertEquals("12...", StringUtil.chop("1234567890", 5));
        assertEquals("123...", StringUtil.chop("1234567890", 6));
        assertEquals("1234...", StringUtil.chop("1234567890", 7));
        assertEquals("12345...", StringUtil.chop("1234567890", 8));
        assertEquals("123456...", StringUtil.chop("1234567890", 9));
        assertEquals("1234567890", StringUtil.chop("1234567890", 10));
        assertEquals("1234567890", StringUtil.chop("1234567890", 11));
        assertEquals("1234567890", StringUtil.chop("1234567890", 12));
    }

    /**
     * Tests {@link StringUtil#trimRight(String)}.
     */
    @Test
    public void testTrimRight() {
        // Test empty stuff
        assertNull(StringUtil.trimRight(null));
        assertEquals("", StringUtil.trimRight(""));
        assertEquals("", StringUtil.trimRight(" "));
        assertEquals("", StringUtil.trimRight("\t"));
        assertEquals("", StringUtil.trimRight("\n"));
        assertEquals("", StringUtil.trimRight("\r"));
        assertEquals("", StringUtil.trimRight("           "));
        // Test without whitespaces
        assertEquals("a", StringUtil.trimRight("a"));
        assertEquals("hello", StringUtil.trimRight("hello"));
        assertEquals("hello world!", StringUtil.trimRight("hello world!"));
        // Test leading whitespaces
        assertEquals("  a", StringUtil.trimRight("  a"));
        assertEquals("  hello", StringUtil.trimRight("  hello"));
        assertEquals("  hello world!", StringUtil.trimRight("  hello world!"));
        // Test right whitespaces
        assertEquals("a", StringUtil.trimRight("a  "));
        assertEquals("hello", StringUtil.trimRight("hello  "));
        assertEquals("hello world!", StringUtil.trimRight("hello world!  "));
        // Test left and right whitespaces
        assertEquals("  a", StringUtil.trimRight("  a "));
        assertEquals("  hello", StringUtil.trimRight("  hello\t"));
        assertEquals("  hello world!", StringUtil.trimRight("  hello world! \t\n "));
    }

    /**
     * Tests {@link StringUtil#fillString(String, char, int)}.
     */
    @Test
    public void testFillString() {
        assertEquals("", StringUtil.fillString(null, '#', 0));
        assertEquals("#", StringUtil.fillString(null, '#', 1));
        assertEquals("##", StringUtil.fillString(null, '#', 2));
        assertEquals("##a", StringUtil.fillString("a", '#', 3));
        assertEquals("#ab", StringUtil.fillString("ab", '#', 3));
        assertEquals("abc", StringUtil.fillString("abc", '#', 3));
        try {
            StringUtil.fillString("abcd", '#', 3);
            fail();
        } catch (IllegalArgumentException e) {
            assertEquals("Text \"abcd\" with length 4 is longer as 3.", e.getMessage());
        }
    }

    /**
     * Tests {@link StringUtil#equalIgnoreWhiteSpace(String, String)}.
     */
    @Test
    public void testEqualIgnoreWhiteSpace() {
        assertTrue(StringUtil.equalIgnoreWhiteSpace(null, null));
        assertFalse(StringUtil.equalIgnoreWhiteSpace("A", null));
        assertFalse(StringUtil.equalIgnoreWhiteSpace(null, "A"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace("", ""));
        assertFalse(StringUtil.equalIgnoreWhiteSpace("A", ""));
        assertFalse(StringUtil.equalIgnoreWhiteSpace("", "A"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace("A", "A"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace(" A", "A"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace("A", "A "));
        assertTrue(StringUtil.equalIgnoreWhiteSpace("A", " A "));
        assertFalse(StringUtil.equalIgnoreWhiteSpace("A", "B"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace("AA", "A A"));
        assertFalse(StringUtil.equalIgnoreWhiteSpace("AA", "AB"));
        assertFalse(StringUtil.equalIgnoreWhiteSpace("A", "AB"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace("A B", "A B"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace("A B C", "A B C"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace("A    B    C", "A\nB\r\tC"));
        assertFalse(StringUtil.equalIgnoreWhiteSpace("A B C", "A B C D"));
        assertFalse(StringUtil.equalIgnoreWhiteSpace("A B C D", "A B C"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace("  A B C", "A B C\t\n"));
        assertTrue(StringUtil.equalIgnoreWhiteSpace(
            "{result=self.doubleValue(_value)@ExistingContractTest; }",
            "{\n  result=self.doubleValue(_value)@ExistingContractTest;\n}"));
    }

    /**
     * Tests {@link StringUtil#toSingleLinedString(String)}
     */
    @Test
    public void testToSingleLinedString() {
        String text = "First Line\nSecond Line\nLine\twith\tTabs\nLast Line";
        assertNull(StringUtil.toSingleLinedString(null));
        assertEquals("", StringUtil.toSingleLinedString(""));
        assertEquals("First Line Second Line Line with Tabs Last Line",
            StringUtil.toSingleLinedString(text));
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
        assertEquals("XBCDXBCDXBCDXBCD", StringUtil.replaceAll(text, new char[] { 'A' }, 'X'));
        assertEquals("AXCDAXCDAXCDAXCD", StringUtil.replaceAll(text, new char[] { 'B' }, 'X'));
        assertEquals("ABXDABXDABXDABXD", StringUtil.replaceAll(text, new char[] { 'C' }, 'X'));
        assertEquals("ABCXABCXABCXABCX", StringUtil.replaceAll(text, new char[] { 'D' }, 'X'));
        assertEquals("ABCDABCDABCDABCD", StringUtil.replaceAll(text, new char[] { 'E' }, 'X'));
        assertEquals("XBXDXBXDXBXDXBXD", StringUtil.replaceAll(text, new char[] { 'A', 'C' }, 'X'));
        assertEquals("XXXXXXXXXXXXXXXX",
            StringUtil.replaceAll(text, new char[] { 'A', 'B', 'C', 'D' }, 'X'));
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
     * Tests {@link StringUtil#repeat(String, int)}
     */
    @Test
    public void testRepeat() {
        // Test line with one character
        try {
            assertEquals("", StringUtil.repeat("#", -1));
            fail();
        } catch (IllegalArgumentException expected) {
        }

        assertEquals("", StringUtil.repeat("#", 0));
        assertEquals("-", StringUtil.repeat("-", 1));
        assertEquals("AA", StringUtil.repeat("A", 2));
        assertEquals("#####", StringUtil.repeat("#", 5));
        // Test line with multiple characters
        assertEquals("ABABAB", StringUtil.repeat("AB", 3));

        // Test null text
        try {
            assertEquals("nullnullnullnull", StringUtil.repeat(null, 4));
            fail();
        } catch (NullPointerException expected) {
        }
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
        assertNull(trim(null));
        assertEquals("AA", trim("AA"));
        assertEquals("AA", trim(" AA "));
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

    @Test
    public void testTestTrim() {
        assertEquals("abc", trim("(abc)", "()"));
        assertEquals("abc", trim("1234567890abc1234567890", Character::isDigit));
        assertEquals("(abc)", trim("(abc)", ""));
        assertEquals("abc)", trim("(abc)", '('));
        assertEquals("abc", trim("(abc)", "()"));
        assertEquals("abc", trim("   \n\t\fabc\n", Character::isWhitespace));
        assertEquals("", trim("abc", it -> true));
        assertEquals("", trim(
            "   \n\t\fa234231hsdafhvnyxcksdaökfhsdaöfhsahövcln231847231 42310897423187sdfsdafbc\n",
            it -> true));
        assertEquals("", trim("", 'c'));

        assertEquals(".", trim("\".\"", '"'));
        assertEquals(".", trim(".", '"'));
        assertEquals(".", trim(".", it -> false));
    }

    @Test
    void testCount() {
        assertEquals(3, count("AbAbA", 0, 5, 'A'));
        assertEquals(2, count("AbAbA", 0, 4, 'A'));
        assertEquals(2, count("AbAbA", 0, 3, 'A'));
        assertEquals(1, count("AbAbA", 0, 2, 'A'));
        assertEquals(1, count("AbAbA", 0, 1, 'A'));
        assertEquals(0, count("AbAbA", 0, 0, 'A'));

        assertEquals(2, count("AbAbA", 1, 5, 'A'));
        assertEquals(2, count("AbAbA", 2, 5, 'A'));
        assertEquals(1, count("AbAbA", 3, 5, 'A'));
        assertEquals(1, count("AbAbA", 4, 5, 'A'));

        assertEquals(0, count("AbAbA", 5, 5, 'A'));
    }
}
