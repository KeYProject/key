package de.uka.ilkd.key.gui.nodeviews;

import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Component;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Insets;
import java.awt.RenderingHints;

import javax.swing.border.AbstractBorder;

public class SequentBorder extends AbstractBorder {

    public static Color darkPurple = new Color(100, 10, 50);
    private static int thickness = 1;
    TitleButton titleButton;
    Insets titleButtonInsets;
    Insets insets = new Insets(4, 2 * thickness + 6,
            2 * thickness + 6, 2 * thickness + 6);
    private int polylineX[] = new int[6];
    private int polylineY[] = new int[6];
    private int polylineIndex = 0;

    SequentBorder(TitleButton titleButton, Insets titleButtonInsets) {
        this.titleButtonInsets = titleButtonInsets;
        this.titleButton = titleButton;
    }

    private void addPoint(int x, int y) {
        polylineX[polylineIndex] = x;
        polylineY[polylineIndex] = y;
        polylineIndex++;
    }

    @Override
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {

        Graphics2D g2d = (Graphics2D) g;
        g2d.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                RenderingHints.VALUE_ANTIALIAS_ON);

        int offsetY = titleButton.getHeight() / 2 + titleButtonInsets.top;
        x += insets.left / 2;
        y += insets.top + offsetY;
        height -= insets.top + insets.bottom / 2 + offsetY;
        width -= insets.left / 2 + insets.right / 2;

        int titleHorizontalPaddings = 14;
        g2d.setColor(darkPurple);

        polylineIndex = 0;

        addPoint(titleButton.getX() - titleHorizontalPaddings, y);

        addPoint(x, y);

        y += height;
        addPoint(x, y);

        x += width;
        addPoint(x, y);

        y -= height;
        addPoint(x, y);

        addPoint(titleButton.getX() + titleButton.getWidth() + titleHorizontalPaddings, y);

        g2d.setColor(darkPurple);
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
