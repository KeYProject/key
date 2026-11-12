/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.util.List;
import javafx.scene.Node;

import de.uka.ilkd.key.gui.fx.MainWindowF;

/**
 * A settings provider is an entry in the settings dialog, counter-part of
 * {@code de.uka.ilkd.key.gui.settings.SettingsProvider} of the Swing module {@code key.ui}.
 * <p>
 * It is displayed within the settings tree by {@link #getDescription()}. Tree children are
 * determined by {@link #getChildProviders()} (named differently than in the Swing original
 * because {@code getChildren} clashes with {@link javafx.scene.Parent#getChildren()}). The most
 * important functions are {@link #apply(MainWindowF)}
 * and {@link #getPanel(MainWindowF)}.
 *
 * @author Alexander Weigl
 */
public interface SettingsProviderF {

    /**
     * A textual human readable description of the settings panel. Used at the overview tree at
     * the left.
     *
     * @return non-null non-empty string
     */
    String getDescription();

    /**
     * Provides the visual component for the right side.
     * <p>
     * This panel will be wrapped inside a {@link javafx.scene.control.ScrollPane}.
     * <p>
     * You are allowed to reuse the returned component, in which case you should update its input
     * components on every call (the Swing originals re-read the settings in
     * {@code getPanel(MainWindow)} as well).
     *
     * @param window the main window, non-null
     * @return the panel node
     */
    Node getPanel(MainWindowF window);

    /**
     * Tree children of your settings provider.
     * <p>
     * Use this method to split your settings into multiple panels; they are displayed as children
     * within the tree. (Swing {@code SettingsProvider.getChildren}; the FX port renames the
     * accessor because {@code getChildren} clashes with
     * {@link javafx.scene.Parent#getChildren()}.)
     *
     * @return non-null list, default returns the empty list
     */
    default List<SettingsProviderF> getChildProviders() {
        return List.of();
    }

    /**
     * The method is called if the settings should be applied to the main window.
     * <p>
     * If the user clicks on Apply or OK, the settings dialog calls this method for every
     * registered provider (including the children). Read your values from the input components
     * and update the settings of the main window. If a field is not in the appropriate format,
     * throw an {@link InvalidSettingsInputExceptionF} with a reference to the panel and the
     * component; this prevents the settings dialog from closing (Swing parity).
     *
     * @param window the main window, non-null
     * @throws InvalidSettingsInputExceptionF if an input component is not properly filled
     */
    void apply(MainWindowF window) throws InvalidSettingsInputExceptionF;

    /**
     * Determines whether the given search string matches this settings provider; matching
     * providers are highlighted in the tree of the settings dialog.
     * <p>
     * The default matches the description (in the Swing module the default is {@code false},
     * which leaves the search without effect for the built-in providers; the description match
     * is the obvious fallback).
     *
     * @param substring a possibly empty, non-null string
     * @return true iff the search should highlight this settings provider
     */
    default boolean contains(String substring) {
        return substring != null && !substring.isEmpty()
                && getDescription().toLowerCase().contains(substring.toLowerCase());
    }

    /**
     * Determines the order in the tree of the settings. Higher values are shown last.
     *
     * @return the priority
     */
    default int getPriorityOfSettings() {
        return 0;
    }
}
