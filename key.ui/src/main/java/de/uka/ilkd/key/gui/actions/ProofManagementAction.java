/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;

/**
 * Shows the proof management dialog
 */
public final class ProofManagementAction extends MainWindowAction {

    /**
     *
     */
    private static final long serialVersionUID = 7696620742992568551L;

    public ProofManagementAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Proof Management");
        setTooltip("Browse contracts and possible proof targets");
        setIcon(IconFactory.proofMgt(16));

        enabledOnAnActiveProof();
    }

    public void actionPerformed(ActionEvent e) {
        showProofManagement();
    }

    private void showProofManagement() {
        if (getMediator().getSelectedProof() == null) {
            mainWindow.notify(new GeneralFailureEvent("Please load a proof first"));
        } else {
            ProofManagementDialog.showInstance(
                getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment());
        }
    }
}
