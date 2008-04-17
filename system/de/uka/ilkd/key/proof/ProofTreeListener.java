// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

public interface ProofTreeListener {

    /** The node mentioned in the ProofTreeEvent has changed, and/or
     * there are new descendants of that node.  Any nodes that are not
     * descendants of that node are unaffected. */
    void proofExpanded(ProofTreeEvent e);

    /** The proof tree has been pruned under the node mentioned in the
     * ProofTreeEvent.  In other words, that node should no longer
     * have any children now.  Any nodes that were not descendants of
     * that node are unaffected.*/
    void proofPruned(ProofTreeEvent e);

    /** The structure of the proof has changed radically.  Any client should
     * rescan the whole proof tree. */
    void proofStructureChanged(ProofTreeEvent e);

    /** The proof trees has been closed (the list of goals is empty).
     */
    void proofClosed(ProofTreeEvent e);

    /** The goal mentioned in the ProofEvent has been removed 
     *from the list of goals.
     */
    void proofGoalRemoved(ProofTreeEvent e);

    /** The goals mentiones in the list of added goals in the proof
     * event have been added to the proof
     */
    void proofGoalsAdded(ProofTreeEvent e);

    /** 
     * The goals mentiones in the list of added goals in the proof
     * event have been added to the proof
     */
    void proofGoalsChanged(ProofTreeEvent e);

}
