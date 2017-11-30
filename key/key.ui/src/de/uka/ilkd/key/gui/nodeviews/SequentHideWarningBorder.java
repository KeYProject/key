package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Color;
import java.awt.Component;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Insets;

import javax.swing.SwingUtilities;
import javax.swing.border.Border;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.SequentPrintFilter;


// XXX Is not updated correctly, yet.
public class SequentHideWarningBorder implements Border {

    private static final String WARNING = "Some formulas have been hidden (by search phrase)";
    private final Color ALERT_COLOR = new Color(255, 178, 178);
    private SequentView sequentView;

    public SequentHideWarningBorder(SequentView sequentView) {
        this.sequentView = sequentView;
    }

    @Override
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {

        System.out.println("SequentHideWarningBorder.paintBorder()");

        SequentPrintFilter filter = sequentView.getFilter();
        if(filter == null) {
            return;
        }

        Sequent originalSequent = filter.getOriginalSequent();
        if(originalSequent == null) {
            return;
        }

        int orgSize = originalSequent.size();
        int newSize = filter.getFilteredAntec().size() + filter.getFilteredSucc().size();
        System.out.println(orgSize + " -> " + newSize);
        if(orgSize == newSize) {
            return;
        }

        // XXX Make decent
        g.setFont(new Font("sans-serif", Font.PLAIN, 12));
        int strWidth = SwingUtilities.computeStringWidth(g.getFontMetrics(), WARNING);

        int lx = (width-strWidth)/2;
        g.setColor(ALERT_COLOR);
        // XXX Make numbers decent
        g.fillRect(lx, 0, strWidth+10, 20);
        g.setColor(Color.BLACK);
        g.drawString(WARNING, lx+5, 12);

    }

    @Override
    public Insets getBorderInsets(Component c) {
        return new Insets(0,0,0,0);
    }

    @Override
    public boolean isBorderOpaque() {
        return false;
    }

}
