package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Color;
import java.awt.Component;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Toolkit;
import java.util.Map;

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

        Map<?, ?> desktopHints = 
                (Map<?, ?>) Toolkit.getDefaultToolkit().getDesktopProperty("awt.font.desktophints");
        
        Graphics2D g2d = (Graphics2D) g;
        if (desktopHints != null) {
            g2d.setRenderingHints(desktopHints);
        }

        g2d.setFont(FONT);
        int strWidth = SwingUtilities.computeStringWidth(g2d.getFontMetrics(), WARNING);

        int lx = (width-strWidth)/2;
        g2d.setColor(ALERT_COLOR);
        g2d.fillRect(lx, 0, strWidth + 2*DELTAX, borderHeight);
        g2d.setColor(Color.BLACK);
        g2d.drawString(WARNING, lx + DELTAX, borderHeight / 2 + 5);

    }
}
