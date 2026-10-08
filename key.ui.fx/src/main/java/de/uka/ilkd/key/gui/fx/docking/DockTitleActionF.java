/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

/**
 * A custom action contributed by a {@link Dockable} to its tab header / tab context menu.
 * <p>
 * Counter-part of the Swing title actions of the module {@code key.ui}: {@code
 * TabPanel.getTitleActions()} (plain Swing {@code Action}s, mapped to bibliothek
 * {@code CButton}s by {@code DockingHelper.translateAction}) and {@code
 * TabPanel.getTitleCActions()} (pre-built bibliothek {@code CAction}s). The Swing actions appear
 * in the dockable's title bar and in its title popup menu; the JavaFX port shows them at the top
 * of the tab context menu (see {@code DockWorkspace#createTabContextMenu}).
 * <p>
 * The toggle flavour of the Swing mapping ({@code DockingHelper.createCheckBox} for actions with
 * {@code Action.SELECTED_KEY}) is not needed yet and intentionally left out; add a boolean field
 * when the first check-style title action (e.g. the KeyboardTaclet options) is ported.
 *
 * @param text the menu label (Swing {@code Action.NAME})
 * @param tooltip the description (Swing {@code Action.SHORT_DESCRIPTION}; unused in the menu, kept
 *        for future tab-header buttons)
 * @param action the action to run (Swing {@code Action.actionPerformed})
 */
public record DockTitleActionF(String text, String tooltip, Runnable action) {

    /**
     * Creates a title action without a tooltip.
     *
     * @param text the menu label
     * @param action the action to run
     */
    public DockTitleActionF(String text, Runnable action) {
        this(text, null, action);
    }
}
