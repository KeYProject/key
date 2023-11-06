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
 * A highlight painter for drawing a squiggly line under the selection. Color and width of the line
 * can be set, although the result may not always look nice since there is no anti-aliasing.
 *
 * @author Wolfram Pfeifer
 */
public class SquigglyUnderlinePainter implements Highlighter.HighlightPainter {
    /** the color of the highlights to paint */
    private final Color highlightColor;

    /** the stroke of the highlights to paint (for the line width) */
    private final Stroke stroke;

    /** the size, i.e., radius, of a single squiggle */
    private final int squiggleSize;

    /**
     * Creates a new SquigglyUnderlinePainter.
     *
     * @param highlightColor the color of the line
     * @param squiggleSize the size (width) of a single arc of the painter
     * @param lineWidth the line width of the squiggle (1 works best)
     */
    public SquigglyUnderlinePainter(Color highlightColor, int squiggleSize, float lineWidth) {
        this.highlightColor = highlightColor;
        stroke = new BasicStroke(lineWidth);
        this.squiggleSize = squiggleSize;
    }

    @Override
    public void paint(Graphics g, int offs0, int offs1, Shape bounds, JTextComponent c) {
        // don't render if empty
        if (offs0 == offs1) {
            return;
        }

        if (bounds != null) {
            try {
                g.setColor(highlightColor);
                if (g instanceof Graphics2D) {
                    ((Graphics2D) g).setStroke(stroke);
                }
                TextUI mapper = c.getUI();
                Rectangle p0 = mapper.modelToView(c, offs0);
                Rectangle p1 = mapper.modelToView(c, offs1);

                int twoSquiggles = squiggleSize * 2;
                int y = p0.y + p0.height - squiggleSize;

                for (int x = p0.x; x <= p0.x + (p1.x - p0.x) - twoSquiggles; x += twoSquiggles) {
                    g.drawArc(x, y, squiggleSize, squiggleSize, 180, -180);
                    g.drawArc(x + squiggleSize, y, squiggleSize, squiggleSize, -180, 180);
                }
            } catch (BadLocationException e) {
                // cannot render
            }
        }
    }
}
