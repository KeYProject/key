/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Proof;

public class ShowUsedContractsAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 2680058046414747256L;

    private final Proof proof;

    public ShowUsedContractsAction(MainWindow mainWindow, Proof proof) {
        super(mainWindow);
        setName("Show Used Contracts");

        getMediator().enableWhenProofLoaded(this);

        this.proof = proof;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        showUsedContracts();
    }

    private void showUsedContracts() {
        Proof currentProof = proof == null ? getMediator().getSelectedProof() : proof;
        if (currentProof == null) {
            mainWindow.notify(new GeneralInformationEvent("No contracts available.",
                "If you wish to see the used contracts "
                    + "for a proof you have to load one first"));
        } else {
            ProofManagementDialog.showInstance(getMediator().getSelectedProof().getInitConfig(),
                getMediator().getSelectedProof());
        }
    }

}
