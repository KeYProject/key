/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.ui.gui.tacletmatch;

/**
 * GUI-independent text helpers for the taclet-match dialog: abbreviation, tooltip escaping and
 * line/column-to-offset mapping. Kept free of any AWT/Swing dependency so the logic can be reused
 * and unit-tested headlessly; the panels only deal with the resulting strings/offsets.
 */
final class TmText {

    private TmText() {}

    /**
     * the first line of {@code s} ({@code ""} for {@code null}); the whole string if single-line.
     */
    static String firstLine(String s) {
        if (s == null) {
            return "";
        }
        int nl = s.indexOf('\n');
        return nl >= 0 ? s.substring(0, nl) : s;
    }

    /**
     * the first line of {@code s}, truncated to {@code limit} characters with an ellipsis appended
     * when it was longer.
     */
    static String truncateFirstLine(String s, int limit) {
        String line = firstLine(s);
        return line.length() > limit ? line.substring(0, limit) + " …" : line;
    }

    /**
     * {@code s} flattened to a single line (newlines become spaces), truncated to {@code limit}
     * characters with an ellipsis appended when it was longer.
     */
    static String collapseToLine(String s, int limit) {
        String oneLine = (s == null ? "" : s).replace('\n', ' ');
        return oneLine.length() > limit ? oneLine.substring(0, limit) + " …" : oneLine;
    }

    /** an escaped, fixed-width HTML tooltip body for possibly long or multi-line {@code s}. */
    static String htmlTooltip(String s) {
        String esc = (s == null ? "" : s).replace("&", "&amp;").replace("<", "&lt;")
                .replace(">", "&gt;").replace("\n", "<br>");
        return "<html><div style='width:480px'>" + esc + "</div></html>";
    }

    /**
     * the character offset into {@code s} of the given 1-based {@code line} and 1-based
     * {@code column}, clamped to {@code [0, s.length()]}.
     */
    static int offsetOf(String s, int line, int column) {
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
