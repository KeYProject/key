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
 * <p>
 * D33 (P3c): the per-view font family/size constants of Swing {@code Config} are mirrored here:
 * the proof tree uses the system font at the current size, the sequent view the monospaced font
 * at the current size, and the goal list / proof list the system font at the fixed
 * {@code sizeFactor * SIZES[2]} (Swing {@code Config.setDefaultFonts}). The Swing family name
 * {@code "Default"} (an AWT synonym for the platform's default face) resolves to the JavaFX
 * logical family {@code "System"}; there are no rendering call-site changes beyond this class —
 * the views keep using the {@link ConfigF#DEFAULT} accessor methods.
 */
public final class ConfigF {

    /** Swing Config key of the proof tree font ({@code KEY_FONT_PROOF_TREE}). */
    public static final String KEY_FONT_PROOF_TREE = "KEY_FONT_PROOF_TREE";
    /** Swing Config key of the sequent view font ({@code KEY_FONT_CURRENT_GOAL_VIEW}). */
    public static final String KEY_FONT_SEQUENT_VIEW = "KEY_FONT_CURRENT_GOAL_VIEW";
    /** Swing Config key of the goal list font ({@code KEY_FONT_GOAL_LIST_VIEW}). */
    public static final String KEY_FONT_GOAL_LIST_VIEW = "KEY_FONT_GOAL_LIST_VIEW";
    /** Swing Config key of the proof list font ({@code KEY_FONT_PROOF_LIST_VIEW}). */
    public static final String KEY_FONT_PROOF_LIST_VIEW = "KEY_FONT_PROOF_LIST_VIEW";

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

    /**
     * @return a font for the proof tree view (Swing {@code KEY_FONT_PROOF_TREE}: family
     *         {@code "Default"} — here the JavaFX logical family {@code "System"} — at the
     *         current base size)
     */
    public Font proofTreeFont() {
        return Font.font("System", baseSize());
    }

    /**
     * @return a font for the goal list view (Swing {@code KEY_FONT_GOAL_LIST_VIEW}: family
     *         {@code "Default"} → {@code "System"} at the fixed {@code sizeFactor * SIZES[2]},
     *         independent of the UI size index)
     */
    public Font goalListFont() {
        return Font.font("System", sizeFactor * SIZES[2]);
    }

    /**
     * @return a font for the proof list view (Swing {@code KEY_FONT_PROOF_LIST_VIEW}: family
     *         {@code "Default"} → {@code "System"} at the fixed {@code sizeFactor * SIZES[2]},
     *         independent of the UI size index)
     */
    public Font proofListFont() {
        return Font.font("System", sizeFactor * SIZES[2]);
    }

    /** @return the index into {@link #SIZES} of the current font size */
    public int sizeIndex() {
        return sizeIndex;
    }
}
