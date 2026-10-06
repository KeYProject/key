/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.configuration;

import javafx.scene.text.Font;

import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * Central definition of fonts and font sizes of the JavaFX UI.
 * <p>
 * Counter-part of {@code de.uka.ilkd.key.gui.configuration.Config} in the Swing module
 * {@code key.ui}. Like the original, the font size is derived from the core
 * {@link ProofIndependentSettings} view settings, so the persisted size index of the Swing UI
 * carries over.
 */
public final class ConfigF {

    /** The available font sizes for the main views, mirroring {@code Config.SIZES}. */
    public static final int[] SIZES = { 10, 12, 14, 17, 20, 24 };

    public static final ConfigF DEFAULT = new ConfigF();

    private final int sizeIndex;
    private final double sizeFactor;

    private ConfigF() {
        sizeIndex = readSizeIndex();
        sizeFactor = readSizeFactor();
    }

    private int readSizeIndex() {
        int s = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().sizeIndex();
        return (s < 0 || s > SIZES.length) ? 0 : s;
    }

    private double readSizeFactor() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getUIFontSizeFactor();
    }

    /** @return the base size of the current font configuration */
    public double baseSize() {
        return sizeFactor * SIZES[sizeIndex];
    }

    /** @return a font for the regular UI text */
    public Font systemFont() {
        return Font.font("System", baseSize());
    }

    /** @return a monospaced font for terminal/sequent style text */
    public Font monoFont() {
        return Font.font("Monospaced", baseSize());
    }

    /** @return a font for the proof tree view */
    public Font proofTreeFont() {
        return Font.font("System", baseSize());
    }

    /** @return the index into {@link #SIZES} of the current font size */
    public int sizeIndex() {
        return sizeIndex;
    }
}
