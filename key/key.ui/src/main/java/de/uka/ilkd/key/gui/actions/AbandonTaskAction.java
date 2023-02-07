/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;

public final class AbandonTaskAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 915588190956945751L;

    public AbandonTaskAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Abandon Proof");
        setIcon(IconFactory.abandon(16));
        setAcceleratorLetter(KeyEvent.VK_W);
        setTooltip("Drop current proof.");

        getMediator().enableWhenProofLoaded(this);
        lookupAcceleratorKey();
    }

    public synchronized void actionPerformed(ActionEvent e) {
        boolean removalConfirmed = getMediator().getUI().confirmTaskRemoval("Are you sure?");
        if (removalConfirmed) {
            getMediator().getSelectedProof().dispose();
        }
    }

}
