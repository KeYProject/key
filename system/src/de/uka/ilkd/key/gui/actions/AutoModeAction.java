// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;

import javax.swing.Action;
import javax.swing.Icon;
import javax.swing.KeyStroke;

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

    private static final KeyStroke START_KEY = KeyStroke.getKeyStroke(KeyEvent.VK_A, InputEvent.CTRL_DOWN_MASK);
	private static final KeyStroke STOP_KEY = KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0);
	/**
     * 
     */
    private static final long serialVersionUID = -7702898691162947994L;
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
        associatedProof = getMediator().getSelectedProof();
        putValue("hideActionText", Boolean.TRUE);
        setName(getStartCommand());
        setTooltip(MainWindow.AUTO_MODE_TEXT);
        setIcon(startLogo);
        setAcceleratorKey(START_KEY);
    
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
        	putValue(Action.ACCELERATOR_KEY, STOP_KEY);
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
        	putValue(Action.ACCELERATOR_KEY, START_KEY);
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
	    // this interface is no longer used (MU)
//	    getMediator().interrupted(e);
	    getMediator().stopAutoMode();
	}
    }

}