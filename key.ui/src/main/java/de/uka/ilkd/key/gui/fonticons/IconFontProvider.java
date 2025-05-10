/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.fonticons;

import java.awt.*;
import javax.swing.*;

import de.uka.ilkd.key.settings.ProofIndependentSettings;

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
        Color color = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isDarkMode()
                ? darkModeColor
                : lightModeColor;
        return IconFontSwing.buildIcon(iconCode, size, color);
    }

    @Override
    String getKey(float size) {
        Color color = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isDarkMode()
                ? darkModeColor
                : lightModeColor;
        return iconCode.toString() + color + size;
    }
}
