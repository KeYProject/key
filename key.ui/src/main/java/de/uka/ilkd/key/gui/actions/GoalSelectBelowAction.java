/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 */
public final class GoalSelectBelowAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 4574670781882014092L;

    /**
     * Creates a new GoalBackAction.
     *
     * @param mainWindow the main window this action belongs to
     * @param longName true iff long names (including the name of the rule to undo) shall be
     *        displayed (e.g. in menu items)
     */
    public GoalSelectBelowAction(MainWindow mainWindow) {
        super(mainWindow);
        setAcceleratorLetter(KeyEvent.VK_J);
        setName("Select Goal Below");
        setIcon(IconFactory.selectGoalBelow(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip(
            "Changes selected goal in the proof-tree to the next item below the current one");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        this.mainWindow.getProofTreeView().selectBelow();
    }
}
