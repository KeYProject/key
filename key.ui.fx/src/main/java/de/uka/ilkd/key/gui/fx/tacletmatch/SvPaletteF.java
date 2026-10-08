/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.tacletmatch;

import javafx.scene.control.Label;

/**
 * Stable colour assignment for schema variables shared across the taclet-match dialog panels, so a
 * variable carries the same colour in the match overview, the instantiation panel and the in-place
 * highlight of the matched term.
 *
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.tacletmatch.SvPalette} (SvPalette.java:20-51). The colours are
 * fixed light chip backgrounds with dark text (highlighter style), kept in code like the Swing
 * original: they are data colours of the highlighter palette, not theme chrome (the Swing javadoc
 * notes theming to the active look-and-feel was deliberately left out; the light pastels stay
 * readable on both themes).
 */
public final class SvPaletteF {

    private static final int[] BG =
        { 0xE1F5EE, 0xEEEDFE, 0xFAEEDA, 0xFBEAF0, 0xE6F1FB, 0xFAECE7 };
    private static final int[] FG =
        { 0x0F6E56, 0x3C3489, 0x854F0B, 0x72243E, 0x0C447C, 0x712B13 };

    private SvPaletteF() {}

    /** number of distinct colours before the palette repeats */
    public static int size() {
        return BG.length;
    }

    /** the chip background colour for the given palette index (repeating) */
    public static javafx.scene.paint.Color background(int index) {
        return rgb(BG[Math.floorMod(index, BG.length)]);
    }

    /** the chip text colour for the given palette index (repeating) */
    public static javafx.scene.paint.Color foreground(int index) {
        return rgb(FG[Math.floorMod(index, FG.length)]);
    }

    /** the 0xRRGGBB constant {@code v} as an RGB colour */
    private static javafx.scene.paint.Color rgb(int v) {
        return javafx.scene.paint.Color.rgb((v >> 16) & 0xFF, (v >> 8) & 0xFF, v & 0xFF);
    }

    /** the background colour as a CSS hex string (for inline {@code -fx-background-color}) */
    public static String backgroundCss(int index) {
        return css(BG[Math.floorMod(index, BG.length)]);
    }

    /** the foreground colour as a CSS hex string (for inline {@code -fx-text-fill}) */
    public static String foregroundCss(int index) {
        return css(FG[Math.floorMod(index, FG.length)]);
    }

    private static String css(int rgb) {
        return String.format("#%06X", rgb);
    }

    /**
     * a chip-styled label for a schema variable name in the given palette colour
     * (SvPalette.chip, SvPalette.java:43-50).
     */
    public static Label chip(String text, int index) {
        Label l = new Label(text);
        l.getStyleClass().add("tacletmatch-chip");
        l.setStyle("-fx-background-color: " + backgroundCss(index) + "; -fx-text-fill: "
            + foregroundCss(index) + ";");
        return l;
    }
}
