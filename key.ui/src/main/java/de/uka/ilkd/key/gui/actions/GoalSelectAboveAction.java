/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 * Action to select the next goal above in the proof tree.
 */
public final class GoalSelectAboveAction extends MainWindowAction {

    private static final long serialVersionUID = 4574670781882014092L;

    /**
     * Creates the new action.
     *
     * @param mainWindow the main window this action belongs to
     */
    public GoalSelectAboveAction(MainWindow mainWindow) {
        super(mainWindow, true);
        setName("Select Goal Above");
        setIcon(IconFactory.selectGoalAbove(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip(
            "Changes selected goal in the proof-tree to the next item above the current one");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        this.mainWindow.getProofTreeView().selectAbove();
    }
}
