package de.uka.ilkd.key.gui.prooftree;

import javax.swing.*;
import java.awt.*;

/**
 * @author Alexander Weigl
 * @version 1 (20.05.19)
 */
public class Style {
    private Color foreground, background, border;
    private int fontStyle;
    private Icon icon;
    private String tooltip, text;

    private boolean fixForeground, fixBackground, fixBorder, fixIcon, fixFontStyle, fixTooltip, fixText;

    public Color getForeground() {
        return foreground;
    }

    public void setForeground(Color foreground) {
        if (fixForeground) return;
        this.foreground = foreground;
    }

    public void setForeground(Color foreground, boolean important) {
        setForeground(foreground);
        if (important) fixForeground = true;
    }

    public Color getBackground() {
        return background;
    }

    public void setBackground(Color background) {
        if (fixBackground) return;
        this.background = background;
    }


    public void setBackground(Color background, boolean important) {
        setBackground(background);
        if (important) fixBackground = true;
    }

    public Color getBorder() {
        return border;
    }

    public void setBorder(Color border) {
        if (fixBorder) return;
        this.border = border;
    }

    public void setBorder(Color border, boolean important) {
        setBorder(border);
        if (important) fixBorder = true;
    }

    public int getFontStyle() {
        return fontStyle;
    }

    public void setFontStyle(int fontStyle) {
        if (fixFontStyle) return;
        this.fontStyle = fontStyle;
    }

    public void setFontStyle(int fontStyle, boolean important) {
        setFontStyle(fontStyle);
        if (important) fixFontStyle = true;
    }

    public Icon getIcon() {
        return icon;
    }

    public void setIcon(Icon icon) {
        if (fixIcon) return;
        this.icon = icon;
    }

    public void setIcon(Icon icon, boolean important) {
        setIcon(icon);
        if (important) fixIcon = true;
    }

    public String getTooltip() {
        return tooltip;
    }

    public void setTooltip(String tooltip) {
        if (fixTooltip) return;
        this.tooltip = tooltip;
    }

    public void setTooltip(String tooltip, boolean important) {
        setTooltip(tooltip);
        if (important) fixTooltip = true;
    }

    public String getText() {
        return text;
    }

    public void setText(String text) {
        if (fixText) return;
        this.text = text;
    }

    public void setText(String text, boolean important) {
        setText(text);
        if (important) fixText = true;
    }

}
