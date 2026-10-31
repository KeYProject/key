/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.docking;

import org.jspecify.annotations.Nullable;

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
 * The toggle flavour of the Swing mapping ({@code DockingHelper.createCheckBox} wraps actions
 * with an {@code Action.SELECTED_KEY} value into check-style bibliothek {@code CCheckBox}es,
 * DockingHelper.java:188-223) is expressed by a non-{@code null} {@link #selected()} value: the
 * host renders such a title action as a checked menu item whose state is given by
 * {@code selected} at menu-build time (the record is immutable — a re-opened menu re-reads the
 * current state, like Swing's {@code CCheckBox} reading {@code Action.SELECTED_KEY}). A
 * {@code null} {@link #selected()} is a plain action button.
 *
 * @param text the menu label (Swing {@code Action.NAME})
 * @param tooltip the description (Swing {@code Action.SHORT_DESCRIPTION}; unused in the menu, kept
 *        for future tab-header buttons)
 * @param selected the checked state of the check-style flavour (Swing {@code Action.SELECTED_KEY}
 *        mapped by {@code DockingHelper.createCheckBox}, DockingHelper.java:188-223), or
 *        {@code null} for a plain action
 * @param action the action to run (Swing {@code Action.actionPerformed})
 */
public record DockTitleActionF(String text, String tooltip, @Nullable Boolean selected,
        Runnable action) {

    /**
     * Creates a title action without a tooltip.
     *
     * @param text the menu label
     * @param action the action to run
     */
    public DockTitleActionF(String text, Runnable action) {
        this(text, null, (Boolean) null, action);
    }

    /**
     * Creates a plain title action with a tooltip.
     *
     * @param text the menu label
     * @param tooltip the description, may be {@code null}
     * @param action the action to run
     */
    public DockTitleActionF(String text, @Nullable String tooltip, Runnable action) {
        this(text, tooltip, (Boolean) null, action);
    }

    /**
     * Creates a check-style title action (Swing {@code DockingHelper.createCheckBox} for actions
     * with {@code Action.SELECTED_KEY}, DockingHelper.java:188-223).
     *
     * @param text the menu label
     * @param selected the initial checked state
     * @param action the action to run
     */
    public DockTitleActionF(String text, boolean selected, Runnable action) {
        this(text, null, Boolean.valueOf(selected), action);
    }
}
