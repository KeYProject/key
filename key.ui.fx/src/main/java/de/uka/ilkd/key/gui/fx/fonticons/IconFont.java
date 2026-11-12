/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.fonticons;

import javafx.scene.text.Font;

/**
 * An icon font that provides glyphs for a set of icons, the JavaFX counter-part of
 * {@code de.uka.ilkd.key.gui.fonticons.IconFont} in the Swing module {@code key.ui}.
 * <p>
 * Implementations are enums whose constants each represent one glyph (see
 * {@link #getUnicode()}). The font is loaded lazily from the module resources via
 * {@link javafx.scene.text.Font#loadFont}.
 */
public interface IconFont {

    /**
     * @return the (cached) {@link Font} carrying the glyphs
     */
    Font getFont();

    /**
     * @return the unicode code point of the glyph in {@link #getFont()}
     */
    char getUnicode();
}
