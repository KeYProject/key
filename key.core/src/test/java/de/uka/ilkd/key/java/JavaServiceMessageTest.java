/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for {@link JavaService#simplifyJavaParserMessage(String)} which turns JavaParser's verbose
 * "Parse error. Found ..., expected one of <long list>" messages into something readable.
 *
 * @author Claude (improveErrorMessages)
 */
class JavaServiceMessageTest {

    @Test
    void rewritesParseErrorLeadIn() {
        String in = "(line 1,col 9) Parse error. Found \";\", expected one of \"!\" \"(\"";
        String out = JavaService.simplifyJavaParserMessage(in);
        assertTrue(out.startsWith("(line 1,col 9) Java syntax error: unexpected \";\""),
            "unexpected: " + out);
        assertFalse(out.contains("Parse error"));
    }

    @Test
    void shortensLongExpectedList() {
        String in = "Parse error. Found \";\", expected one of "
            + "\"a\" \"b\" \"c\" \"d\" \"e\" \"f\" \"g\" \"h\"";
        String out = JavaService.simplifyJavaParserMessage(in);
        assertTrue(out.endsWith("..."), "long list should be truncated: " + out);
        // keeps the first six alternatives, drops the rest
        assertTrue(out.contains("\"f\""));
        assertFalse(out.contains("\"g\""));
    }

    @Test
    void leavesShortListsIntact() {
        String in = "Parse error. Found \";\", expected one of \"a\" \"b\"";
        String out = JavaService.simplifyJavaParserMessage(in);
        assertEquals("Java syntax error: unexpected \";\", expected one of \"a\" \"b\"", out);
    }

    @Test
    void leavesSemanticMessagesUnchanged() {
        String in = "Cannot resolve type Foo";
        assertEquals(in, JavaService.simplifyJavaParserMessage(in));
    }

    @Test
    void dropsJavaCardSchemaAlternatives() {
        String in = "Parse error. Found \";\", expected one of "
            + "\"#abortJavaCardTransaction\" \"#beginJavaCardTransaction\" \"!\" \"(\"";
        String out = JavaService.simplifyJavaParserMessage(in);
        assertFalse(out.contains("#abortJavaCardTransaction"),
            "JavaCard/schema tokens should be dropped: " + out);
        assertTrue(out.contains("\"!\"") && out.contains("\"(\""),
            "relevant alternatives should remain: " + out);
    }

    @Test
    void collapsesMultiLineOffendingToken() {
        // the offending token is an (escaped) multi-line comment; JavaParser writes "Found \"...\""
        // with two spaces, so the message reads "unexpected \"...\"" - the cleanup must still match
        String in = "Parse error. Found  \"/*@ loop_invariant 0 <= i\\n @ && x\\n @*/\", "
            + "expected one of \"!\" \"(\"";
        String out = JavaService.simplifyJavaParserMessage(in);
        assertFalse(out.contains("\\n"), "escaped newlines should be collapsed: " + out);
        assertFalse(out.contains("\n"), "real newlines should be collapsed: " + out);
        assertTrue(out.startsWith("Java syntax error: unexpected"), out);
    }

    @Test
    void humanizesUnsolvedSymbolJargon() {
        String out = JavaService.humanizeJavaParserJargon("Unsolved symbol : Foobar");
        assertFalse(out.contains("Unsolved symbol"), "jargon should be removed: " + out);
        assertTrue(out.contains("Cannot resolve 'Foobar'"), out);
        assertTrue(out.contains("check for typos"), out);
    }

    @Test
    void humanizeLeavesOtherTextUnchanged() {
        assertEquals("all good", JavaService.humanizeJavaParserJargon("all good"));
    }
}
