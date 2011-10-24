package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
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
	setName("Proof Management...");
	setTooltip("Proof Management.");
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
	return getMediator().getProof() != null
	        && getMediator().getProof().getJavaModel() != null
	        && !getMediator().getProof().getJavaModel().isEmpty();
    }

    public void actionPerformed(ActionEvent e) {
	showProofManagement();
    }

    private void showProofManagement() {
	if (getMediator().getProof() == null) {
	    getMediator().notify(
		    new GeneralFailureEvent("Please load a proof first"));
	} else {
	    ProofManagementDialog.showInstance(getMediator().getProof().env()
		    .getInitConfig());
	}
    }
}
