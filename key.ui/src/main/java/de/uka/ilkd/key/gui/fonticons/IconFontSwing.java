/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.fonticons;

import java.awt.*;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;
import javax.swing.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public final class IconFontSwing {
    private static final Logger LOGGER = LoggerFactory.getLogger(IconFontSwing.class);

    /**
     * Builds an image.
     *
     * @param iconCode the icon code.
     * @param size the size.
     * @return the image.
     */
    public static Image buildImage(IconFont iconCode, float size) {
        return buildImage(iconCode, size, Color.BLACK);
    }

    /**
     * Builds an image.
     *
     * @param iconCode the icon code.
     * @param size the size.
     * @param color the size.
     * @return the image.
     */
    public static Image buildImage(IconFont iconCode, float size, Color color) {
        Font font = buildFont(iconCode, size);
        String text = Character.toString(iconCode.getUnicode());
        return buildImage(text, font, color);
    }

    /**
     *
     * @param iconCode
     * @param size
     * @param color
     * @return
     */
    public static Image buildImage(IconFont iconCode, float size, Color color, double rotation) {
        Image img = buildImage(iconCode, size, color);
        BufferedImage newImage =
            new BufferedImage((int) size, (int) size, BufferedImage.TYPE_INT_RGB);
        Graphics2D graphics = (Graphics2D) newImage.getGraphics();
        AffineTransform transform = new AffineTransform();
        transform.rotate(rotation, size / 2, size / 2);
        graphics.drawImage(img, transform, null);
        return img;
    }

    /**
     * Builds an icon.
     *
     * @param iconCode the icon code.
     * @param size the size.
     * @return the icon.
     */
    public static Icon buildIcon(IconFont iconCode, float size) {
        return buildIcon(iconCode, size, Color.BLACK);
    }

    /**
     * Builds an icon.
     *
     * @param iconCode the icon code.
     * @param size the size.
     * @param color the size.
     * @return the icon.
     */
    public static Icon buildIcon(IconFont iconCode, float size, Color color) {
        return new ImageIcon(buildImage(iconCode, size, color));
    }

    private static BufferedImage buildImage(String text, Font font, Color color) {
        JLabel label = new JLabel(text);
        label.setForeground(color);
        label.setFont(font);
        Dimension dim = label.getPreferredSize();
        int width = dim.width + 1;
        int height = dim.height + 1;
        label.setSize(width, height);
        BufferedImage bufImage = new BufferedImage(width, height, BufferedImage.TYPE_INT_ARGB);
        Graphics2D g2d = bufImage.createGraphics();
        g2d.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,
            RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
        g2d.setRenderingHint(RenderingHints.KEY_FRACTIONALMETRICS,
            RenderingHints.VALUE_FRACTIONALMETRICS_ON);
        label.print(g2d);
        g2d.dispose();
        return bufImage;
    }

    private static Font buildFont(IconFont iconCode, float size) {
        try {
            Font f = iconCode.getFont();
            return f.deriveFont(size);
        } catch (Exception e) {
            LOGGER.warn("Building font failed", e);
            return new Font(Font.MONOSPACED, Font.PLAIN, (int) size);
        }
    }
}
