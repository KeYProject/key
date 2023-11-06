/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.proof.Proof;

/**
 * Saves the current selected proof.
 */
public final class SaveFileAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = -5479654127272775831L;

    public SaveFileAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Save...");
        setIcon(IconFactory.saveFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Save current proof.");
        mainWindow.getMediator().enableWhenProofLoaded(this);
    }

    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getMediator().ensureProofLoaded()) {
            // Try to save back to file where proof was initially loaded from
            final Proof selectedProof = mainWindow.getMediator().getSelectedProof();
            mainWindow.getUserInterface().saveProof(selectedProof, ".proof");
        } else {
            mainWindow.popupWarning("No proof.", "Oops...");
        }
    }
}
