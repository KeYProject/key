/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

/**
 * GUI-independent text helpers for the taclet-match dialog: abbreviation, line counting and
 * line/column-to-offset mapping.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.TmText} (TmText.java:12-75), which is already
 * free of AWT/Swing; only the class name changed. The panels deal only with the resulting
 * strings/offsets.
 */
public final class TmTextF {

    private TmTextF() {}

    /**
     * the first line of {@code s} ({@code ""} for {@code null}); the whole string if single-line
     * (TmText.java:19-25).
     */
    public static String firstLine(String s) {
        if (s == null) {
            return "";
        }
        int nl = s.indexOf('\n');
        return nl >= 0 ? s.substring(0, nl) : s;
    }

    /**
     * {@code s} flattened to a single line and truncated to {@code limit} characters with an
     * ellipsis appended when it was longer. Every run of whitespace (the newlines and the alignment
     * indentation the pretty-printer inserts when it wraps a term) collapses to a single space, so
     * a multi-line formula reads as one continuous line instead of a stub followed by blank gaps
     * (TmText.java:34-37).
     */
    public static String collapseToLine(String s, int limit) {
        String oneLine = (s == null ? "" : s).replaceAll("\\s+", " ").trim();
        return oneLine.length() > limit ? oneLine.substring(0, limit) + " …" : oneLine;
    }

    /** the number of lines in {@code s} (newline count + 1; {@code 1} for {@code null}/empty) */
    public static int lineCount(String s) {
        if (s == null || s.isEmpty()) {
            return 1;
        }
        int lines = 1;
        for (int i = 0; i < s.length(); i++) {
            if (s.charAt(i) == '\n') {
                lines++;
            }
        }
        return lines;
    }

    /**
     * the character offset into {@code s} of the given 1-based {@code line} and 1-based
     * {@code column}, clamped to {@code [0, s.length()]} (TmText.java:64-74).
     */
    public static int offsetOf(String s, int line, int column) {
        int i = 0;
        int ln = 1;
        while (ln < line && i < s.length()) {
            if (s.charAt(i) == '\n') {
                ln++;
            }
            i++;
        }
        return Math.max(0, Math.min(i + column - 1, s.length()));
    }
}
