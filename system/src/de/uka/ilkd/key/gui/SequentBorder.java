package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.nodeviews.InnerNodeView;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Component;
import java.awt.FontMetrics;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Insets;
import java.awt.RenderingHints;
import javax.swing.UIManager;

import javax.swing.border.AbstractBorder;

public class SequentBorder extends AbstractBorder {

    protected int thickness = 2;
    protected Color lineColor = Color.RED;
    SequentView sequentView;
    public int xForHighLight, yForHighLight, offset, offset2;

    public SequentBorder(SequentView sequentView) {
        this.sequentView = sequentView;
    }

    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {

        Graphics2D g2d = (Graphics2D) g;
        g2d.setFont(UIManager.getFont(Config.KEY_FONT_CURRENT_GOAL_VIEW));
        FontMetrics fm = c.getFontMetrics(g2d.getFont());
        g2d.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                RenderingHints.VALUE_ANTIALIAS_ON);
        offset = 0;
        offset2 = 0;
        x += 15;
        y += 15;
        width -= 30;
        height -= 30;

        // Case InnerNodeView
        if (sequentView instanceof InnerNodeView) {
            offset = 40;
            offset2 = 16;

            InnerNodeView inw = (InnerNodeView) sequentView;

            g2d.setColor(new Color(250, 90, 90));
            if (inw.showTaclet) {
                g2d.fillRect(x + width - offset + 6,
                        y - 15 + 9, offset, offset2);
            } else {
                g2d.drawRect(x + width - offset + 6,
                        y - 15 + 9, offset, offset2);
            }

            g2d.setColor(Color.BLACK);
            g2d.drawString("\u22A2",
                    x + width - offset / 2 - fm.charWidth('\u22A2') / 2 + 6,
                    y - 15 + 9 + offset2 / 2 + fm.getHeight() / 3);
        }

        // needs to be done after offset change
        xForHighLight = x + width - offset + thickness / 2;
        yForHighLight = y + offset2 - thickness / 2;

        int omitTop = fm.stringWidth(sequentView.getTitle());
        int titleHorizontalPaddings = 10;
        g2d.setColor(Color.BLACK);
        g2d.drawString(
                sequentView.getTitle(), x + 35 + titleHorizontalPaddings,
                y + fm.getHeight() / 3);


        g2d.setColor(lineColor);
        g2d.setStroke(new BasicStroke(thickness));
        drawHorizontalLine(x, y, 35, g2d);
        drawHorizontalLine(x + 35 + omitTop + 2 * titleHorizontalPaddings, y,
                width - offset - omitTop - 35 - 2 * titleHorizontalPaddings, g2d);
        drawHorizontalLine(x, y + height, width, g2d);
        drawHorizontalLine(x + width - offset, y + offset2, offset, g2d);

        drawVerticalLine(x, y, height, g2d);
        drawVerticalLine(x + width, y + offset2, height - offset2, g2d);
        drawVerticalLine(x + width - offset, y, offset2, g2d);

    }

    void drawHorizontalLine(int x, int y, int length, Graphics2D g2d) {
        g2d.drawLine(x, y, x + length, y);
    }

    void drawVerticalLine(int x, int y, int length, Graphics2D g2d) {
        g2d.drawLine(x, y, x, y + length);
    }

    @Override
    public Insets getBorderInsets(Component c) {
        return new Insets(thickness + 33, thickness + 33,
                thickness + 33, thickness + 33);
    }
}
