/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.tacletmatch;

import java.awt.*;
import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.border.CompoundBorder;
import javax.swing.border.EmptyBorder;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.gui.fonticons.FontAwesomeSolid;
import de.uka.ilkd.key.gui.fonticons.IconFontSwing;

/**
 * Shared styling for the taclet-match dialog panels. Uses the active look-and-feel's fonts and
 * colours (so it follows Metal or FlatLaf), only nudging sizes and spacing for readability and
 * clearer section separation.
 */
final class TmStyle {

    /** logic/term text is rendered a couple of points larger than the default for legibility */
    private static final int FONT_BUMP = 2;

    private TmStyle() {}

    /** a monospaced font for logic/term text, slightly larger than the component's default. */
    static Font mono(Component c) {
        int size = (c != null && c.getFont() != null) ? c.getFont().getSize() : 12;
        return new Font(Font.MONOSPACED, Font.PLAIN, size + FONT_BUMP);
    }

    /** the muted foreground used for captions and labels. */
    static Color muted() {
        Color c = UIManager.getColor("Label.disabledForeground");
        return c != null ? c : Color.GRAY;
    }

    /** whether the active look-and-feel is FlatLaf (vs. Metal or another classic L&amp;F). */
    static boolean isFlat() {
        return UIManager.getLookAndFeel().getClass().getName().toLowerCase().contains("flat");
    }

    /** the separator/hairline colour of the active L&amp;F, with sensible fallbacks. */
    private static Color sepColor() {
        Color c = UIManager.getColor("Separator.foreground");
        if (c == null) {
            c = UIManager.getColor("controlShadow");
        }
        return c != null ? c : Color.GRAY;
    }

    /** linear blend of two colours ({@code t=0} → a, {@code t=1} → b). */
    static Color blend(Color a, Color b, float t) {
        return new Color(Math.round(a.getRed() * (1 - t) + b.getRed() * t),
            Math.round(a.getGreen() * (1 - t) + b.getGreen() * t),
            Math.round(a.getBlue() * (1 - t) + b.getBlue() * t));
    }

    /**
     * a faint band colour, used to set the concrete matched term apart from the schematic find and
     * the bindings without drawing a box.
     */
    static Color tint() {
        Color bg = UIManager.getColor("Panel.background");
        if (bg == null) {
            bg = new Color(0xECECEC);
        }
        return blend(bg, sepColor(), 0.14f);
    }

    /**
     * separates the footer's button bar from the content above, adapting to the active L&amp;F:
     * FlatLaf gets a faint surface bar under a hairline (its modern dialog idiom); a classic
     * L&amp;F
     * (Metal) gets an engraved shadow/highlight rule, which reads more clearly against its greys.
     */
    static void styleFooter(JComponent footer) {
        Color sep = sepColor();
        if (isFlat()) {
            Color bg = UIManager.getColor("Panel.background");
            footer.setOpaque(true);
            if (bg != null) {
                footer.setBackground(blend(bg, sep, 0.06f));
            }
            footer.setBorder(new CompoundBorder(BorderFactory.createMatteBorder(1, 0, 0, 0, sep),
                new EmptyBorder(10, 12, 10, 12)));
        } else {
            Color shadow = UIManager.getColor("controlShadow");
            Color hi = UIManager.getColor("controlLtHighlight");
            if (shadow == null) {
                shadow = sep;
            }
            Border rule = hi != null
                    ? new CompoundBorder(BorderFactory.createMatteBorder(1, 0, 0, 0, shadow),
                        BorderFactory.createMatteBorder(1, 0, 0, 0, hi))
                    : BorderFactory.createMatteBorder(1, 0, 0, 0, shadow);
            footer.setBorder(new CompoundBorder(rule, new EmptyBorder(8, 12, 8, 12)));
        }
    }

    /**
     * A small, unobtrusive disclosure (expand/collapse) toggle, used uniformly across the dialog so
     * every "show more" affordance looks and behaves the same. Collapsed shows {@code ▸}, expanded
     * {@code ▾}; update it with {@link #setDisclosure(JButton, boolean)}.
     *
     * @param what what the toggle reveals, for the tooltip (e.g. "the full sequent"); {@code null}
     *        for a generic "Show more/less"
     */
    static JButton disclosure(String what) {
        JButton b = new JButton();
        b.setFocusable(false);
        b.setBorderPainted(false);
        b.setContentAreaFilled(false);
        b.setMargin(new Insets(0, 3, 0, 3));
        b.putClientProperty("tm.what", what);
        setDisclosure(b, false);
        return b;
    }

    static void setDisclosure(JButton b, boolean expanded) {
        b.setIcon(IconFontSwing.buildIcon(
            expanded ? FontAwesomeSolid.CARET_DOWN : FontAwesomeSolid.CARET_RIGHT, 12f, muted()));
        Object what = b.getClientProperty("tm.what");
        if (what == null) {
            b.setToolTipText(expanded ? "Show less" : "Show more");
        } else {
            b.setToolTipText((expanded ? "Hide " : "Show ") + what);
        }
    }

    /**
     * a titled section border with a bold title, inner padding and a gap below, so the dialog's
     * sections read as clearly separated cards while still using the L&amp;F's border style.
     */
    static Border section(String title) {
        // a bold section header with a hairline rule beneath it and whitespace below — no box.
        // Only the result preview keeps an actual surface (its card), so it reads as "the answer".
        Color rule = UIManager.getColor("Separator.foreground");
        if (rule == null) {
            rule = UIManager.getColor("controlShadow");
        }
        Border underline = BorderFactory.createMatteBorder(1, 0, 0, 0,
            rule != null ? rule : Color.LIGHT_GRAY);
        TitledBorder tb = BorderFactory.createTitledBorder(underline, title);
        tb.setTitlePosition(TitledBorder.ABOVE_TOP);
        Font f = tb.getTitleFont();
        if (f != null) {
            tb.setTitleFont(f.deriveFont(Font.BOLD, f.getSize2D() + 1f));
        }
        return new CompoundBorder(new EmptyBorder(2, 0, 14, 0),
            new CompoundBorder(tb, new EmptyBorder(6, 2, 2, 2)));
    }
}
