/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import javax.swing.plaf.TextUI;
import javax.swing.text.BadLocationException;
import javax.swing.text.Highlighter;
import javax.swing.text.JTextComponent;

/**
 * A highlight painter that marks an error span with a light translucent background fill and a
 * squiggly underline in the given color.
 * <p>
 * Unlike a plain range highlighter, it also renders a <em>zero-width</em> highlight (when
 * {@code offs0 == offs1}) - e.g. the insertion point right after a construct where a missing
 * {@code ')'} or {@code ';'} belongs - by drawing a fixed, one-character-wide mark at that spot.
 * This is needed because such an insertion point usually sits at the end of a line, where there is
 * no glyph to underline.
 *
 * @author Wolfram Pfeifer (original squiggle painter)
 */
public class ErrorMarkPainter implements Highlighter.HighlightPainter {
    /** the color of the squiggle */
    private final Color lineColor;
    /** the translucent fill color (derived from {@link #lineColor}) */
    private final Color fillColor;
    /** the radius of a single squiggle arc */
    private final int squiggleSize = 2;

    /**
     * @param color the (opaque) color of the underline; the background uses a translucent tint of
     *        it
     * @param alpha the alpha (0-255) of the background fill
     */
    public ErrorMarkPainter(Color color, int alpha) {
        this.lineColor = color;
        this.fillColor = new Color(color.getRed(), color.getGreen(), color.getBlue(), alpha);
    }

    @Override
    public void paint(Graphics g, int offs0, int offs1, Shape bounds, JTextComponent c) {
        if (bounds == null) {
            return;
        }
        try {
            TextUI mapper = c.getUI();
            Rectangle p0 = mapper.modelToView(c, offs0);
            int x0 = p0.x;
            int x1;
            if (offs1 > offs0) {
                Rectangle p1 = mapper.modelToView(c, offs1);
                // same line and to the right: use the real extent; otherwise (range crossed a line
                // break, e.g. the span reached an end-of-line) fall back to a fixed width.
                x1 = (p1.y == p0.y && p1.x > p0.x) ? p1.x : x0 + caretWidth(c);
            } else {
                // zero-width insertion point: a fixed one-character mark
                x1 = x0 + caretWidth(c);
            }
            int width = Math.max(1, x1 - x0);

            g.setColor(fillColor);
            g.fillRect(x0, p0.y, width, p0.height);

            g.setColor(lineColor);
            if (g instanceof Graphics2D g2) {
                g2.setStroke(new BasicStroke(1f));
            }
            int two = squiggleSize * 2;
            int y = p0.y + p0.height - squiggleSize;
            for (int x = x0; x <= x1 - two; x += two) {
                g.drawArc(x, y, squiggleSize, squiggleSize, 180, -180);
                g.drawArc(x + squiggleSize, y, squiggleSize, squiggleSize, -180, 180);
            }
        } catch (BadLocationException e) {
            // cannot render
        }
    }

    /** Width of the fixed one-character mark used for zero-width / end-of-line positions. */
    private static int caretWidth(JTextComponent c) {
        FontMetrics fm = c.getFontMetrics(c.getFont());
        return Math.max(fm.charWidth(' '), 5);
    }
}
