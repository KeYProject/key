/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.nodeviews.CurrentGoalView;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.pp.PosInSequent;

/**
 * Copy a term that is currently selected (i.e., under the mouse cursor) in the current goal view to
 * the default system clip board.
 *
 * @author bruns
 */
public class CopyToClipboardAction extends MainWindowAction {

    private static final long serialVersionUID = -6193181877353785015L;

    public CopyToClipboardAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Copy to clipboard");
        setTooltip("Copy a selected sequent term into your default clipboard.\n"
            + "This functionality may depend on your window manager or installed clipboard managers.\n"
            + "The default clipboard is not the 'middle click clipboard' on X window systems.");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        CurrentGoalView goalView = mainWindow.getGoalView();
        if (goalView == null) {
            return;
        }
        PosInSequent pis = goalView.getMousePosInSequent();
        if (pis == null) {
            return;
        }
        GuiUtilities.copyHighlightToClipboard(goalView, pis);
    }
}
