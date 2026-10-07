/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.util.List;

import javafx.scene.Node;

/**
 * A single entry of the KeY settings dialog, counter-part of {@code SettingsProvider} of the
 * Swing module {@code key.ui}.
 * <p>
 * The provider supplies a human readable description (shown in the settings tree), a category
 * (grouping in the tree), and a JavaFX panel building the input controls. When the user accepts
 * the dialog, {@link #apply()} is invoked for every provider; implementors must transfer the
 * values of their input components into the respective settings.
 */
public interface SettingsProviderF {

    /**
     * @return a human readable description shown in the settings tree
     */
    String getDescription();

    /**
     * @return the name of the category group in the settings tree
     */
    String getCategory();

    /**
     * Provides the panel shown on the right side of the settings dialog when this provider is
     * selected.
     *
     * @return a fresh panel; may also be reused, in which case it must be updated on selection
     */
    Node getPanel();

    /**
     * Transfers the values of the panel's input components into the corresponding settings.
     * Called for every provider when the user accepts or applies the settings.
     */
    void apply();

    /**
     * Restores the values shown in the panel to the values currently stored in the settings.
     */
    default void reset() {
    }

    /**
     * @return provider-specific sub categories/panels, empty if none
     */
    default List<SettingsProviderF> getChildren() {
        return List.of();
    }
}
