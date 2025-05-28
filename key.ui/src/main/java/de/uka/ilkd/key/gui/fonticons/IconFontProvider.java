/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.fonticons;

import java.awt.*;
import javax.swing.*;

public class IconFontProvider extends IconProvider {
    private final IconFont iconCode;
    private final Color lightModeColor;
    private final Color darkModeColor;

    public IconFontProvider(IconFont iconCode) {
        this(iconCode, Color.black, Color.white);
    }

    public IconFontProvider(IconFont iconCode, Color color) {
        this(iconCode, color, color);
    }

    public IconFontProvider(IconFont iconCode, Color lightModeColor, Color darkModeColor) {
        this.iconCode = iconCode;
        this.lightModeColor = lightModeColor;
        this.darkModeColor = darkModeColor;
    }

    @Override
    Icon load(float size) {
        Icon darkMode = IconFontSwing.buildIcon(iconCode, size, darkModeColor);
        Icon lightMode = IconFontSwing.buildIcon(iconCode, size, lightModeColor);
        return new LightDarkIcon(lightMode, darkMode);
    }

    @Override
    String getKey(float size) {
        return iconCode.toString() + size;
    }
}
