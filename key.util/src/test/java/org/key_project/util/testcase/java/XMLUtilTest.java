/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.testcase.java;

import java.util.LinkedList;
import java.util.List;

import org.key_project.util.java.StringUtil;
import org.key_project.util.java.XMLUtil;
import org.key_project.util.java.XMLUtil.ITagReplacer;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Tests for {@link XMLUtil}.
 *
 * @author Martin Hentschel
 */
public class XMLUtilTest {
    /**
     * Tests {@link XMLUtil#replaceTags(String, org.key_project.util.java.XMLUtil.ITagReplacer)}.
     */
    @Test
    public void testReplaceTags() {
        assertNull(XMLUtil.replaceTags(null, null));
        assertNull(XMLUtil.replaceTags("Hello", null));
        assertNull(XMLUtil.replaceTags(null, new LoggingReplacer("|")));
        assertReplaceTags("Hello World", "Hello World", "|");
        assertReplaceTags("<html>Hello<br> World</html>", "|Hello| World|", "|", "<html>", "<br>",
            "</html>");
        assertReplaceTags("Hello World", "Hello World", null);
        assertReplaceTags("<html>Hello<br> World</html>", "Hello World", null, "<html>", "<br>",
            "</html>");
        assertReplaceTags("<html>Hello<br /> World", "|Hello| World", "|", "<html>", "<br />");
        assertReplaceTags("Hello<br/> World</html>", "Hello| World|", "|", "<br/>", "</html>");
        assertReplaceTags("<html a=\"b\" c='x'>Hello World</html>", "|Hello World|", "|",
            "<html a=\"b\" c='x'>", "</html>");
        assertReplaceTags("<html a=\"<<>>>\" c='>'>Hello World</html>", "|Hello World|", "|",
            "<html a=\"<<>>>\" c='>'>", "</html>");
    }

    /**
     * Executes a test step of {@link #testReplaceTags()}.
     *
     * @param text The text to execute
     *        {@link XMLUtil#replaceTags(String, org.key_project.util.java.XMLUtil.ITagReplacer)}
     *        on.
     * @param expectedResult The expected result.
     * @param fixedReplacement The fixed replacement to use.
     * @param expectedTags The expected found tags.
     */
    protected void assertReplaceTags(String text, String expectedResult, String fixedReplacement,
            String... expectedTags) {
        LoggingReplacer replacer = new LoggingReplacer(fixedReplacement);
        String result = XMLUtil.replaceTags(text, replacer);
        assertEquals(expectedResult, result);
        assertEquals(expectedTags.length, replacer.getLog().size());
        int i = 0;
        for (String tag : expectedTags) {
            assertEquals(expectedTags[i], tag);
            i++;
        }
    }

    /**
     * An {@link ITagReplacer} which logs the found tags.
     *
     * @author Martin Hentschel
     */
    public static class LoggingReplacer implements ITagReplacer {
        /**
         * The found tags.
         */
        private final List<String> log = new LinkedList<>();

        /**
         * The fixed replacement to use.
         */
        private final String fixedReplacement;

        /**
         * Constructor.
         *
         * @param fixedReplacement The fixed replacement to use.
         */
        public LoggingReplacer(String fixedReplacement) {
            this.fixedReplacement = fixedReplacement;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String replaceTag(String tag) {
            log.add(tag);
            return fixedReplacement;
        }

        /**
         * Returns the found tags.
         *
         * @return The found tags.
         */
        public List<String> getLog() {
            return log;
        }
    }

    /**
     * Tests {@link XMLUtil#removeTags(String)}
     */
    @Test
    public void testRemoveTags() {
        assertNull(XMLUtil.removeTags(null));
        assertEquals("Hello World", XMLUtil.removeTags("Hello World"));
        assertEquals("Hello World", XMLUtil.removeTags("<html>Hello<br> World</html>"));
        assertEquals("Hello World", XMLUtil.removeTags("<html>Hello<br /> World"));
        assertEquals("Hello World", XMLUtil.removeTags("Hello<br/> World</html>"));
        assertEquals("Hello World", XMLUtil.removeTags("<html a=\"b\" c='x'>Hello World</html>"));
        assertEquals("Hello World",
            XMLUtil.removeTags("<html a=\"<<>>>\" c='>'>Hello World</html>"));
    }

    /**
     * Tests {@link XMLUtil#encodeText(String)}
     */
    @Test
    public void testEncodeText() {
        // Test null
        assertNull(XMLUtil.encodeText(null));
        // Test empty string
        assertEquals(StringUtil.EMPTY_STRING, XMLUtil.encodeText(StringUtil.EMPTY_STRING));
        // Text XML tags
        assertEquals("&lt;hello&gt;world&lt;/hello&gt;",
            XMLUtil.encodeText("<hello>world</hello>"));
        // Test XML attributes
        assertEquals("&lt;hello a=&quot;A&quot; b=&apos;B&apos;&gt;world&lt;/hello&gt;",
            XMLUtil.encodeText("<hello a=\"A\" b='B'>world</hello>"));
        // Test XML entities
        assertEquals(
            "&lt;hello a=&quot;A&quot; b=&apos;B&apos;&gt;&amp;lt;world&amp;gt;&lt;/hello&gt;",
            XMLUtil.encodeText("<hello a=\"A\" b='B'>&lt;world&gt;</hello>"));
    }
}
