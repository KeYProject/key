package de.uka.ilkd.key.gui.fonticons;

import javax.swing.*;
import java.awt.*;

public class IconFontProvider extends IconProvider {
    private final IconFont iconCode;
    private final Color color;

    public IconFontProvider(IconFont iconCode) {
        this(iconCode, Color.black);
    }

    public IconFontProvider(IconFont iconCode, Color color) {
        this.iconCode = iconCode;
        this.color = color;
    }

    @Override
    Icon load(float size) {
        return IconFontSwing.buildIcon(iconCode, size, color);
    }

    @Override
    String getKey(float size) {
        return iconCode.toString() + color + size;
    }
}
