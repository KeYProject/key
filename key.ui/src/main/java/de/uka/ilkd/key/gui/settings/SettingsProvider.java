/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.util.Collections;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * A settings provider is an entry in an {@link SettingsUi}.
 * <p>
 * It will be display within the settings tree by {@link #getDescription()}. Tree children are
 * determined by {@link #getChildren()}. The most important functions are:
 * {@link #applySettings(MainWindow)} and {@link #getPanel(MainWindow)}.
 *
 * @author Alexander Weigl
 * @version 1 (08.04.19)
 * @since 2.8.0
 */
public interface SettingsProvider {
    /**
     * A textual human readable description of the settings panel. Used at the overview tree at the
     * left.
     *
     * @return non-null non-empty string
     */
    String getDescription();

    /**
     * Provides the visual component for the right side.
     * <p>
     * This panel will be wrapped inside a {@link JScrollPane}.
     * <p>
     * You are allowed to reuse the return component. But then you should update the components,
     * e.g. text field, during handling of the call.
     *
     * @param window non-null reference
     * @return
     */
    JComponent getPanel(MainWindow window);

    /**
     * Tree children of your settings dialog.
     * <p>
     * You can use this method, if you need to split your settings into multiple panels. The
     * children are displayed as children within the {@link javax.swing.JTree}.
     *
     * @return non-null list, default returns the empty list
     */
    default List<SettingsProvider> getChildren() {
        return Collections.emptyList();
    }

    /**
     * The method is called if the settings should be applied to the {@link MainWindow}.
     * <p>
     * If the user clicks on apply or accept, the {@link SettingsDialog} calls this method for every
     * registered {@link SettingsProvider}.
     * <p>
     * You should read your values from the input components and update the settings within the main
     * window. If a field is not in the appropiate format, you should throw an
     * {@link InvalidSettingsInputException} with the reference to the panel and component.
     *
     * @throws InvalidSettingsInputException if an input component is not properly fill. Prevent the
     *         settings dialog from closing.
     */
    void applySettings(MainWindow window) throws InvalidSettingsInputException;

    /**
     * An icon for this settings for the {@link JTree}.
     *
     * @return nullable
     * @deprecated unused currently
     */
    @Deprecated
    default Icon getIcon() {
        return null;
    }

    /**
     * Determines if the given search string matches some your settings.
     * <p>
     * Implement this function for search support. The settings dialog ask every provider if a user
     * given search request is "handled" by a settings provider.
     *
     * @param substring a possible empty, non-null string
     * @return true iff the search should highlight your settings provider.
     */
    default boolean contains(String substring) {
        return false;
    }

    /**
     * Determines the order in the {@link JTree} of the settings.
     * Higher values are shown last.
     *
     * @return
     */
    default int getPriorityOfSettings() {
        return 0;
    }
}
