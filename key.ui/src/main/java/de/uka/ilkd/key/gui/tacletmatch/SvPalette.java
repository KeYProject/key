/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.awt.*;
import javax.swing.*;
import javax.swing.border.EmptyBorder;

/**
 * Stable colour assignment for schema variables shared across the taclet-match dialog panels, so a
 * variable carries the same colour in the match overview, the instantiation panel and (later) the
 * in-place highlight of the matched term.
 *
 * <p>
 * The colours are fixed light chip backgrounds with dark text (highlighter style), readable on both
 * light and dark look-and-feels; theming them to the active L&amp;F is left for later.
 */
public final class SvPalette {

    private static final int[] BG =
        { 0xE1F5EE, 0xEEEDFE, 0xFAEEDA, 0xFBEAF0, 0xE6F1FB, 0xFAECE7 };
    private static final int[] FG =
        { 0x0F6E56, 0x3C3489, 0x854F0B, 0x72243E, 0x0C447C, 0x712B13 };

    private SvPalette() {}

    /** number of distinct colours before the palette repeats */
    public static int size() {
        return BG.length;
    }

    public static Color background(int index) {
        return new Color(BG[Math.floorMod(index, BG.length)]);
    }

    public static Color foreground(int index) {
        return new Color(FG[Math.floorMod(index, FG.length)]);
    }

    /** a chip-styled label for a schema variable name in the given palette colour. */
    public static JLabel chip(String text, int index) {
        JLabel l = new JLabel(text);
        l.setOpaque(true);
        l.setBackground(background(index));
        l.setForeground(foreground(index));
        l.setBorder(new EmptyBorder(1, 6, 1, 6));
        return l;
    }
}
