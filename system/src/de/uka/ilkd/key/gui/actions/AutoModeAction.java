package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.Action;
import javax.swing.Icon;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;

public final class AutoModeAction extends MainWindowAction {

    final Icon startLogo = IconFactory
	    .autoModeStartLogo(MainWindow.TOOLBAR_ICON_SIZE);
    final Icon stopLogo = IconFactory.autoModeStopLogo(MainWindow.TOOLBAR_ICON_SIZE);

    private Proof associatedProof;

    private final ProofTreeListener ptl = new ProofTreeAdapter() {

	public void proofStructureChanged(ProofTreeEvent e) {
	    if (e.getSource() == associatedProof) {
		enable();
	    }
	}

	public void proofClosed(ProofTreeEvent e) {
	    if (e.getSource() == associatedProof) {
		enable();
	    }
	}

	public void proofGoalsAdded(ProofTreeEvent e) {
	    Proof p = e.getSource();
	    ImmutableList<Goal> newGoals = e.getGoals();
	    // Check for a closed goal ...
	    if ((newGoals.size() == 0) && (!p.closed())) {
		// No new goals have been generated ...
		mainWindow.setStatusLine("1 goal closed, " + p.openGoals().size()
		        + " remaining");
	    }
	}
    };

    public AutoModeAction(MainWindow mainWindow) {
        super(mainWindow);
        associatedProof = getMediator().getProof();
        putValue("hideActionText", Boolean.TRUE);
        setName(getStartCommand());
        setTooltip(MainWindow.AUTO_MODE_TEXT);
        setIcon(startLogo);
        setAcceleratorLetter(KeyEvent.VK_A);
    
        enable();
    
        if (associatedProof != null
                && !associatedProof.containsProofTreeListener(ptl)) {
            associatedProof.addProofTreeListener(ptl);
        }
    
        getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            /** focused node has changed */
            public void selectedNodeChanged(KeYSelectionEvent e) {
            }
    
            /**
             * the selected proof has changed. Enable or disable action
             * depending whether a proof is available or not
             */
            public void selectedProofChanged(KeYSelectionEvent e) {
        	if (associatedProof != null) {
        	    associatedProof.removeProofTreeListener(ptl);
        	}
    
        	associatedProof = e.getSource().getSelectedProof();
        	enable();
    
        	if (associatedProof != null) {
        	    associatedProof.addProofTreeListener(ptl);
        	}
            }
        });
    
        getMediator().addAutoModeListener(new AutoModeListener() {
    
            /**
             * invoked if automatic execution has started
             */
            public void autoModeStarted(ProofEvent e) {
        	if (associatedProof != null) {
        	    associatedProof.removeProofTreeListener(ptl);
        	}
        	putValue(Action.NAME, "Stop");
        	putValue(Action.SMALL_ICON, stopLogo);
            }
    
            /**
             * invoked if automatic execution has stopped
             */
            public void autoModeStopped(ProofEvent e) {
        	if (associatedProof != null && associatedProof == e.getSource()
        	        && !associatedProof.containsProofTreeListener(ptl)) {
        	    associatedProof.addProofTreeListener(ptl);
        	}
        	putValue(Action.NAME, getStartCommand());
        	putValue(Action.SMALL_ICON, startLogo);
            }
    
        });
    
    }
    
    public void enable() {
	setEnabled(associatedProof != null && !associatedProof.closed());
    }

    private String getStartCommand() {
	if (associatedProof != null && !associatedProof.root().leaf()) {
	    return "Continue";
	} else {
	    return "Start";
	}
    }

    public void actionPerformed(ActionEvent e) {
	// Unfortunately, when clicking the button twice
	// (very fast), the glasspane won't be quick
	// enough to catch the second event. Therefore
	// we make a second check (which is a %%%HACK)
	if (!mainWindow.frozen)
	    getMediator().startAutoMode();
	else {
	    getMediator().interrupted(e);
	    getMediator().stopAutoMode();
	}
    }

}
