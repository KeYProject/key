/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.pp.PosInSequent;

/**
 * The menu shown by a {@link InnerNodeViewListener} when the user clicks on an
 * {@link InnerNodeView}.
 */
public class InnerNodeViewMenu extends SequentViewMenu<InnerNodeView> {
    private static final long serialVersionUID = 1593837287234052754L;

    /**
     * Creates an empty menu.
     */
    InnerNodeViewMenu() {}

    /**
     * Creates a new menu that displays all applicable actions at the given position
     *
     * @param sequentView the SequentView that is the parent of this menu
     * @param pos the PosInSequent
     */
    InnerNodeViewMenu(InnerNodeView sequentView, PosInSequent pos) {
        super(sequentView, pos);

        createMenu(new MenuControl());
    }

    /**
     * Creates the menu by adding all sub-menus and items.
     *
     * @param control the action listener.
     */
    private void createMenu(MenuControl control) {
        addActionListener(control);
        addExtensionMenu();
        addSeparator();
        addClipboardItem(control);
    }
}
