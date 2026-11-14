/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fonticons;

import java.awt.Component;
import java.awt.Graphics;
import javax.swing.Icon;

import de.uka.ilkd.key.settings.ProofIndependentSettings;

/// An icon that switches between light/dark depending the current [ViewSettings].
/// @param dark
/// @param light
record LightDarkIcon(Icon light, Icon dark) implements Icon {
    LightDarkIcon {
        assert (light.getIconHeight() == dark.getIconHeight());
        assert (light.getIconWidth() == dark.getIconWidth());
    }

    @Override
    public void paintIcon(Component c, Graphics g, int x, int y) {
        var isDarkMode = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isDarkMode();
        var icon = isDarkMode ? dark : light;
        icon.paintIcon(c, g, x, y);
    }

    @Override
    public int getIconWidth() {
        return light.getIconWidth();
    }

    @Override
    public int getIconHeight() {
        return light.getIconHeight();
    }
}
