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
	setName("Show Used Contracts...");
	
	getMediator().enableWhenProofLoaded(this);

    }

    @Override
    public void actionPerformed(ActionEvent e) {
	showUsedContracts();
    }

    private void showUsedContracts() {
	Proof currentProof = getMediator().getProof();
	if (currentProof == null) {
		mainWindow
		    .notify(
		            new GeneralInformationEvent(
		                    "No contracts available.",
		                    "If you wish to see the used contracts "
		                            + "for a proof you have to load one first"));
	} else {
	    ProofManagementDialog.showInstance(getMediator(), getMediator().getProof().env()
		    .getInitConfig(), getMediator().getProof());
	}
    }

}
