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
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofManagementDialog;
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
	setAcceleratorLetter(KeyEvent.VK_M);

	setEnabled(enabled());

	getMediator().addKeYSelectionListener(new KeYSelectionListener() {
	    /** focused node has changed */
	    public void selectedNodeChanged(KeYSelectionEvent e) {
	    }

	    /**
	     * the selected proof has changed. Enable or disable action
	     * depending whether a proof is available or not
	     */
	    public void selectedProofChanged(KeYSelectionEvent e) {
		setEnabled(enabled());
	    }
	});
    }

    private boolean enabled() {
	return getMediator().getSelectedProof() != null
	        && getMediator().getSelectedProof().getServices().getJavaModel() != null
	        && !getMediator().getSelectedProof().getServices().getJavaModel().isEmpty();
    }

    public void actionPerformed(ActionEvent e) {
	showProofManagement();
    }

    private void showProofManagement() {
	if (getMediator().getSelectedProof() == null) {
	    mainWindow.notify(
		    new GeneralFailureEvent("Please load a proof first"));
	} else {
	    ProofManagementDialog
                    .showInstance(getMediator().getSelectedProof().getEnv().getInitConfigForEnvironment());
	}
    }
}