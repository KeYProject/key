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

import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.gui.AutoModeListener;
import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.KeYSelectionEvent;
import de.uka.ilkd.key.gui.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;

@SuppressWarnings("serial")

/**
 * This action is one part of the previous UndoLastStepAction: Only enabled when the last node is selected
 *
 * The action is enabled if a goal is selected. 
 */
public final class GoalBackAction extends MainWindowAction {

    /**
     * 
     */
    private boolean longName = false;
    
    /**
     * creates an undo action
     * 
     * @param longName
     *            a boolean true iff the long name should be shown (e.g. in
     *            MenuItems)
     */
    public GoalBackAction(MainWindow mainWindow, boolean longName) {
	super(mainWindow);
	this.longName = longName;
	init();
	setBackMode();
    }

    /** 
     * Registers the action at some listeners to update its status
     * in a correct fashion. This method has to be invoked after the
     * Main class has been initialised with the KeYMediator.
     */
    public void init() {
        final KeYSelectionListener selListener = new KeYSelectionListener() {

            public void selectedNodeChanged(KeYSelectionEvent e) {
                final Proof proof = getMediator().getSelectedProof();
                if (proof == null) {
                    // no proof loaded
                    setEnabled(false);
                } else {
                    final Goal selGoal = getMediator().getSelectedGoal();
                    final Node selNode = getMediator().getSelectedNode();
                    /* we undo the last rule application, if
                     * the goal refers not to the proof's root and the node is not a closed goal node */
                    setEnabled(selNode != proof.root() && !selNode.isClosed());
                }
            }
            
            public void selectedProofChanged(KeYSelectionEvent e) {
                selectedNodeChanged(e);
            }                
        };
        
        getMediator().addKeYSelectionListener(selListener);
        
        getMediator().addAutoModeListener(new AutoModeListener() {
            public void autoModeStarted(ProofEvent e) {
                getMediator().removeKeYSelectionListener(selListener);
                setEnabled(false);
            }

            public void autoModeStopped(ProofEvent e) {
                getMediator().addKeYSelectionListener(selListener);
                selListener.selectedNodeChanged(null);
            }                
        });
        selListener.selectedNodeChanged(new KeYSelectionEvent(getMediator().getSelectionModel()));
    }
    
    private void setBackMode() {
        String appliedRule = "";

        if (longName && getMediator() != null) {
    	final Node nd = getMediator().getSelectedNode();
        
    	if (nd != null && nd.parent() != null 
    		&&  nd.parent().getAppliedRuleApp() != null) {
    	    appliedRule = 
    		" (" + nd.parent().getAppliedRuleApp().rule().displayName() + ")";
    	}
        }
        putValue(NAME, "Goal Back" + appliedRule );
        
        putValue(SMALL_ICON, 
                IconFactory.goalBackLogo(MainWindow.TOOLBAR_ICON_SIZE));
        putValue(SHORT_DESCRIPTION, "Undo the last rule application.");
        putValue(ACCELERATOR_KEY, KeyStroke.getKeyStroke(KeyEvent.VK_Z,
    	    Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()));
    }
    
    public void actionPerformed(ActionEvent e) {            
        Goal selGoal = getMediator().getSelectedGoal();
        
        final Node selNode = getMediator().getSelectedNode();
        if(!selNode.isClosed()){
       	    if (selGoal == null) {
       		    assert(selNode != null);
       		    selGoal = getMediator().getSelectedProof().getSubtreeGoals(selNode).reverse().head();
       	    }        
       	    getMediator().setBack(selGoal);
        }
    }   	
}