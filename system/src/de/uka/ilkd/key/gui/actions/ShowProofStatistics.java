package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.util.Iterator;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

public class ShowProofStatistics extends MainWindowAction {

    /**
     * 
     */
    private static final long serialVersionUID = -8814798230037775905L;

    public ShowProofStatistics(MainWindow mainWindow) {
	super(mainWindow);
	setName("Show Proof Statistics...");
	
	getMediator().enableWhenProofLoaded(this);

    }

    @Override
    public void actionPerformed(ActionEvent e) {
	final Proof proof = getMediator().getSelectedProof();
        if(proof == null) {
            mainWindow.notify(new GeneralInformationEvent("No statistics available.",
                    "If you wish to see the statistics "
                    + "for a proof you have to load one first"));
        } else {
	    String stats = proof.statistics();

	    int interactiveSteps = computeInteractiveSteps(proof.root());                  
	    stats += "Interactive Steps: " +interactiveSteps;

	    JOptionPane.showMessageDialog(mainWindow, 
		    stats,
		    "Proof Statistics", JOptionPane.INFORMATION_MESSAGE);
	}
    }
    
    // helper
    private static int computeInteractiveSteps(Node node) {
        int steps = 0;
        final Iterator<Node> it = node.childrenIterator();
        while (it.hasNext()) {
          steps += computeInteractiveSteps(it.next());
        }
        
        if (node.getNodeInfo().getInteractiveRuleApplication()) {
            steps++;
        }
        return steps;
    }

}
