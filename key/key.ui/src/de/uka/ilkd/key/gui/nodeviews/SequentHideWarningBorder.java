package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Color;
import java.awt.Component;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Insets;
import java.beans.PropertyChangeEvent;

import javax.swing.JComponent;
import javax.swing.SwingUtilities;
import javax.swing.border.TitledBorder;

/**
 * A special purpose border that prints a warning window if the search bar
 * filtering removes formulas from the display.
 *
 * @see SequentView#isHiding()
 *
 * @author Mattias Ulbrich
 */
@SuppressWarnings("serial")
public class SequentHideWarningBorder extends TitledBorder {

    /** The constant color is used as background for the window. */
    private static final Color ALERT_COLOR = new Color(255, 178, 178);

    /** The constant is used to write the warning. */
    private static final Font FONT = new Font("sans-serif", Font.PLAIN, 12);

    /** The warning message which is printed. */
    private static final String WARNING =
            "Some formulas have been hidden (by search phrase)";

    /** The margin left to the box, horizontally. */
    private static final int DELTAX = 5;

    /** The component being shown */
    private SequentView sequentView;

    /** The height of the original border text */
    private int borderHeight;

    /**
     * Instantiates a new sequent border.
     *
     * @param title
     *            the title to display
     * @param sequentView
     *            the sequent view which will be wrapped by the component
     */
    public SequentHideWarningBorder(String title, SequentView sequentView) {
        super(title);
        this.sequentView = sequentView;
        this.borderHeight = getBorderInsets(sequentView).top;
    }

    @Override
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {

        super.paintBorder(c, g, x, y, width, height);
        if (!sequentView.isHiding()) {
            return;
        }

        Graphics g2 = g;
        // g2 = g.create();
        // g2.setClip(0, 0, width, height);

        g2.setFont(FONT);
        int strWidth = SwingUtilities.computeStringWidth(g2.getFontMetrics(), WARNING);

        int lx = (width-strWidth)/2;
        g2.setColor(ALERT_COLOR);
        g2.fillRect(lx, 0, strWidth + 2*DELTAX, borderHeight);
        g2.setColor(Color.BLACK);
        g2.drawString(WARNING, lx + DELTAX, borderHeight / 2 + 5);

    }
}
