package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.prooftree.ProofTreeView;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;

public final class AbandonTaskAction extends MainWindowAction {

    public AbandonTaskAction(MainWindow mainWindow) {
	super(mainWindow);
	setName("Abandon");
	setAcceleratorLetter(KeyEvent.VK_W);
	setTooltip("Drop current proof.");

	getMediator().enableWhenProof(this);
    }

    public void actionPerformed(ActionEvent e) {
	closeTask();
    }
    
    private void closeTask() {
	final Proof proof = getMediator().getProof();
	
	if (proof != null) {
	    final TaskTreeNode rootTask = proof.getBasicTask().getRootTask();
	    closeTask(rootTask); 
	}
    }

    protected void closeTask(TaskTreeNode rootTask) {
       if(mainWindow.getProofList().removeTask(rootTask)){
            for(Proof proof:rootTask.allProofs()){
                //In a previous revision the following statement was performed only
                //on one proof object, namely on: mediator.getProof()
                proof.getServices().getSpecificationRepository().removeProof(proof);
                proof.mgt().removeProofListener();
            }
            mainWindow.getProofView().removeProofs(rootTask.allProofs());
       }
    }


}
