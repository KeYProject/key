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

package de.uka.ilkd.key.proof;

/** An abstract adapter class for receiving proof tree events.  
 * <code>proofStructureChanged</code> has an empty implementation, the
 * other methods delegate to <code>proofStructureChanged</code>.
 *
 * <p>Extend this class to create a ProofTreeEvent listener and 
 * override the implementation of <code>proofStructureChanged</code>
 * to provide a simple reaction to any kind of event, or also
 * override the other methods to provide more fine-grained actions.
 */

public abstract class ProofTreeAdapter implements ProofTreeListener {

    /** The node mentioned in the ProofTreeEvent has changed, and/or
     * there are new descendants of that node.  Any nodes that are not
     * descendants of that node are unaffected. */
    public void proofExpanded(ProofTreeEvent e) {
	proofStructureChanged(e);
    }

    /** The proof tree under the node mentioned in the ProofTreeEvent
     * is in pruning phase. The subtree of node will be removed after this
     * call but at this point the subtree can still be
     * traversed (e.g. in order to free the nodes in caches).
     * The method proofPruned is called, when the nodes are disconnect from
     * node.
     */
    public void proofIsBeingPruned(ProofTreeEvent e){
        
    }
    
    /** The proof tree has been pruned under the node mentioned in the
     * ProofTreeEvent.  In other words, that node should no longer
     * have any children now.  Any nodes that were not descendants of
     * that node are unaffected.*/
    public void proofPruned(ProofTreeEvent e) {
	proofStructureChanged(e);
    }

    /** The structure of the proof has changed radically.  Any client should
     * rescan the whole proof tree. */
    public void proofStructureChanged(ProofTreeEvent e) {
	// empty
    }

    /** The proof trees has been closed (the list of goals is empty).
     */
    public void proofClosed(ProofTreeEvent e) {
	proofStructureChanged(e);
    }

    /** The goal mentioned in the ProofTreeEvent has been removed 
     *from the list of goals.
     */
    public void proofGoalRemoved(ProofTreeEvent e) {
	proofStructureChanged(e);
    }

    /** The goals mentiones in the list of added goals in the proof
     * event have been added to the proof
     */
    public void proofGoalsAdded(ProofTreeEvent e) {
	proofStructureChanged(e);
    }

    /** The goals mentiones in the list of added goals in the proof
     * event have been added to the proof
     */
    public void proofGoalsChanged(ProofTreeEvent e) {
	proofStructureChanged(e);
    }

    /**If, e.g., an SMT Solver was applied to node/goal referenced in e, then 
     * this event occurs in order to monitor, e.g. by a dialog, the result
     * of the SMT solver. The data from the SMT solver can be accessed via.
     * {@code Node.getCounterExData()}*/
    public void smtDataUpdate(ProofTreeEvent e){}
}