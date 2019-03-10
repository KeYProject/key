package de.uka.ilkd.key.gui.fonticons;

import javax.swing.*;
import java.awt.*;
import java.awt.image.BufferedImage;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;

/*
 * Copyright (c) 2016 jIconFont <BR>
 * <BR>
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:<BR>
 * <BR>
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.<BR>
 * <BR>
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
public final class IconFontSwing {

    private static List<IconFont> fonts = new ArrayList<>();

    static {
        fonts.add(FontAwesome.getIconFont());
        fonts.add(FontAwesomeBold.getIconFont());
        fonts.add(Typicons.getIconFont());
        fonts.add(Entypo.getIconFont());
    }


    private IconFontSwing() {
    }

    /**
     * Register an icon font.
     *
     * @param iconFont the icon font.
     */
    public static synchronized void register(IconFont iconFont) {
        if (!IconFontSwing.fonts.contains(iconFont)) {
            IconFontSwing.fonts.add(iconFont);
        }
    }

    /**
     * Builds a font.
     *
     * @param fontFamily the font family.
     * @return the font.
     */
    public static synchronized final Font buildFont(String fontFamily) {
        try {
            for (IconFont iconFont : IconFontSwing.fonts) {
                if (iconFont.getFontFamily().equals(fontFamily)) {
                    return Font.createFont(Font.TRUETYPE_FONT, iconFont.getFontInputStream());
                }
            }
        } catch (Exception ex) {
            Logger.getLogger(IconFontSwing.class.getName()).log(Level.SEVERE,
                    "Font load failure", ex);
        }

        Logger.getLogger(IconFontSwing.class.getName()).log(Level.SEVERE,
                "Font not found: " + fontFamily);
        throw new IllegalArgumentException("Font not found: " + fontFamily);
    }

    /**
     * Builds an image.
     *
     * @param iconCode the icon code.
     * @param size     the size.
     * @return the image.
     */
    public static Image buildImage(IconCode iconCode, float size) {
        return buildImage(iconCode, size, Color.BLACK);
    }

    /**
     * Builds an image.
     *
     * @param iconCode the icon code.
     * @param size     the size.
     * @param color    the size.
     * @return the image.
     */
    public static Image buildImage(IconCode iconCode, float size, Color color) {
        Font font = buildFont(iconCode, size);
        String text = Character.toString(iconCode.getUnicode());
        return buildImage(text, font, color);
    }

    /**
     * Builds an icon.
     *
     * @param iconCode the icon code.
     * @param size     the size.
     * @return the icon.
     */
    public static Icon buildIcon(IconCode iconCode, float size) {
        return buildIcon(iconCode, size, Color.BLACK);
    }

    /**
     * Builds an icon.
     *
     * @param iconCode the icon code.
     * @param size     the size.
     * @param color    the size.
     * @return the icon.
     */
    public static Icon buildIcon(IconCode iconCode, float size, Color color) {
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
        BufferedImage bufImage =
                new BufferedImage(width, height, BufferedImage.TYPE_INT_ARGB);
        Graphics2D g2d = bufImage.createGraphics();
        g2d.setRenderingHint(
                RenderingHints.KEY_TEXT_ANTIALIASING,
                RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
        g2d.setRenderingHint(
                RenderingHints.KEY_FRACTIONALMETRICS,
                RenderingHints.VALUE_FRACTIONALMETRICS_ON);
        label.print(g2d);
        g2d.dispose();
        return bufImage;
    }

    private static Font buildFont(IconCode iconCode, float size) {
        Font font = IconFontSwing.buildFont(iconCode.getFontFamily());
        return font.deriveFont(size);
    }
}