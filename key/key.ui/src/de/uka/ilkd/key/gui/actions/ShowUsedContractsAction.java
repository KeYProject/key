// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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

    public ShowUsedContractsAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show Used Contracts");
	
	getMediator().enableWhenProofLoaded(this);

    }

    @Override
    public void actionPerformed(ActionEvent e) {
	showUsedContracts();
    }

    private void showUsedContracts() {
	Proof currentProof = getMediator().getSelectedProof();
	if (currentProof == null) {
		mainWindow
		    .notify(
		            new GeneralInformationEvent(
		                    "No contracts available.",
		                    "If you wish to see the used contracts "
		                            + "for a proof you have to load one first"));
	} else {
            ProofManagementDialog.showInstance
                    (getMediator().getSelectedProof().getInitConfig(), getMediator().getSelectedProof());
	}
    }

}