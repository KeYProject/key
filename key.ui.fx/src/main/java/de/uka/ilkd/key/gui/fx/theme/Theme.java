/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.theme;

/**
 * The visual themes of the JavaFX UI, replacing the FlatLaf look and feels of the Swing module
 * {@code key.ui}.
 * <p>
 * Each theme refers to a CSS file living in this package; the stylesheet is applied as an
 * additional user agent stylesheet by {@link ThemeManager}. The JavaFX CSS engine is the theming
 * mechanism of key.ui.fx (no FXML).
 */
public enum Theme {
    /** Light theme, close to the FlatLightLaf look of the Swing UI. */
    LIGHT("key-light.css"),

    /** Dark theme, close to the FlatDarkLaf look of the Swing UI. */
    DARK("key-dark.css");

    private final String stylesheet;

    Theme(String stylesheet) {
        this.stylesheet = stylesheet;
    }

    /**
     * @return the resource URL of the theme stylesheet (relative to this class)
     */
    public String stylesheetUrl() {
        return Theme.class.getResource(stylesheet).toExternalForm();
    }

    /** @return whether this is a dark theme */
    public boolean isDark() {
        return this == DARK;
    }
}
