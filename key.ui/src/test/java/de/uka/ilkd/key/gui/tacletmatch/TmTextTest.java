/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Unit tests for {@link TmText}, the GUI-independent text helpers of the taclet-match dialog. No
 * AWT/Swing is touched, so these run headlessly.
 */
public class TmTextTest {

    @Test
    public void firstLine() {
        assertEquals("", TmText.firstLine(null));
        assertEquals("", TmText.firstLine(""));
        assertEquals("abc", TmText.firstLine("abc"));
        assertEquals("a", TmText.firstLine("a\nb\nc"));
        assertEquals("", TmText.firstLine("\nb"), "a leading newline yields an empty first line");
        assertEquals("a", TmText.firstLine("a\n"), "a trailing newline keeps the content line");
    }

    @Test
    public void collapseToLine() {
        assertEquals("a b c", TmText.collapseToLine("a\nb\nc", 80), "newlines become spaces");
        assertEquals("abc", TmText.collapseToLine("abc", 3), "length exactly at the limit");
        assertEquals("a b …", TmText.collapseToLine("a\nb\nc", 3),
            "flattened first, then truncated by character count");
        assertEquals("a & b", TmText.collapseToLine("a\n        &   b", 80),
            "wrapped-formula indentation collapses to a single space");
        assertEquals("x", TmText.collapseToLine("\n  x\n  ", 80),
            "leading and trailing whitespace is trimmed");
        assertEquals("", TmText.collapseToLine(null, 5));
    }

    @Test
    public void htmlTooltip() {
        assertEquals("<html><div style='width:480px'>plain</div></html>",
            TmText.htmlTooltip("plain"));
        assertEquals("<html><div style='width:480px'>a&amp;b&lt;c&gt;d</div></html>",
            TmText.htmlTooltip("a&b<c>d"), "the ampersand must be escaped before < and >");
        assertEquals("<html><div style='width:480px'>a<br>b</div></html>",
            TmText.htmlTooltip("a\nb"), "newlines become <br>");
        assertEquals("<html><div style='width:480px'></div></html>", TmText.htmlTooltip(null));
    }

    @Test
    public void offsetOfSingleLine() {
        assertEquals(0, TmText.offsetOf("hello", 1, 1), "1-based line/column, start of text");
        assertEquals(4, TmText.offsetOf("hello", 1, 5));
        assertEquals(5, TmText.offsetOf("hello", 1, 6), "column at the end of the line");
        assertEquals(5, TmText.offsetOf("hello", 1, 99), "column past the end is clamped");
        assertEquals(0, TmText.offsetOf("hello", 1, 0), "column 0 clamps to 0 (not negative)");
    }

    @Test
    public void offsetOfMultiLine() {
        String s = "ab\ncde";
        assertEquals(0, TmText.offsetOf(s, 1, 1));
        assertEquals(3, TmText.offsetOf(s, 2, 1), "start of the second line is just after '\\n'");
        assertEquals(5, TmText.offsetOf(s, 2, 3), "third char of the second line");
        assertEquals(6, TmText.offsetOf(s, 2, 4), "end of the second line");
        assertEquals(6, TmText.offsetOf(s, 9, 1), "a line past the end clamps to the length");
    }

    @Test
    public void lineCount() {
        assertEquals(1, TmText.lineCount(null));
        assertEquals(1, TmText.lineCount(""));
        assertEquals(1, TmText.lineCount("one line"));
        assertEquals(2, TmText.lineCount("a\nb"));
        assertEquals(3, TmText.lineCount("a\nb\nc"));
        assertEquals(3, TmText.lineCount("a\nb\n"), "a trailing newline still bounds a third line");
    }

}
