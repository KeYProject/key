package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.configuration.Config;
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

    private int thickness = 1;
    String title;
    TacletButton tacletButton;
    Insets insets = new Insets(4, 2 * thickness + 6,
            2 * thickness + 6, 2 * thickness + 6);
    private int polylineX[] = new int[6];
    private int polylineY[] = new int[6];
    private int polylineIndex = 0;

    SequentBorder(String title, TacletButton tacletButton) {
        this.title = title;
        this.tacletButton = tacletButton;
    }

    private void addPoint(int x, int y) {
        polylineX[polylineIndex] = x;
        polylineY[polylineIndex] = y;
        polylineIndex++;
    }

    @Override
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {

        Graphics2D g2d = (Graphics2D) g;
        g2d.setFont(UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW));
        FontMetrics fm = c.getFontMetrics(g2d.getFont());
        g2d.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                RenderingHints.VALUE_ANTIALIAS_ON);

        int offsetY = tacletButton.getHeight() / 2;
        x += insets.left / 2;
        y += insets.top + tacletButton.getHeight() / 2;
        height -= insets.top + insets.bottom / 2 + offsetY;
        width -= insets.left / 2 + insets.right / 2;

        int titleHorizontalPaddings = 10;
        int indentLeft = 35;
        g2d.setColor(Color.black);
        g2d.drawString(title, x + indentLeft + titleHorizontalPaddings,
                y + fm.getHeight() / 3);

        polylineIndex = 0;

        addPoint(x + indentLeft, y);

        addPoint(x, y);

        y += height;
        addPoint(x, y);

        x += width;
        addPoint(x, y);

        y -= height;
        addPoint(x, y);

        x -= width - fm.stringWidth(title) - 2 * titleHorizontalPaddings
                - indentLeft;
        addPoint(x, y);

        g2d.setColor(new Color(100,10,50));
        g2d.setStroke(new BasicStroke(thickness));
        g2d.drawPolyline(polylineX, polylineY, polylineX.length);

    }

    void drawHorizontalLine(int x, int y, int length, Graphics2D g2d) {
        g2d.drawLine(x, y, x + length, y);
    }

    void drawVerticalLine(int x, int y, int length, Graphics2D g2d) {
        g2d.drawLine(x, y, x, y + length);
    }

    @Override
    public Insets getBorderInsets(Component c) {
        return insets;
    }
}
