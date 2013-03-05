package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;

public final class AbandonTaskAction extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = 915588190956945751L;

    public AbandonTaskAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Abandon");
	setAcceleratorLetter(KeyEvent.VK_W);
	setTooltip("Drop current proof.");

	getMediator().enableWhenProofLoaded(this);
    }

    public synchronized void actionPerformed(ActionEvent e) {
    	boolean removalConfirmed =
                getMediator().getUI().confirmTaskRemoval("Are you sure?");
        if (removalConfirmed) {
            getMediator().getUI().removeProof(getMediator().getProof());
        }
    }
    
}
