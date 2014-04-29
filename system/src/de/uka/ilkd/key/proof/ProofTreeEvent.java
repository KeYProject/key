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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;

/** Encapsulates information describing changes to a proof tree, and
 * used to notify proof tree listeners of the change.  
 */

public class ProofTreeEvent {

    private Proof source;
    private Node  node;
    private Goal  goal;
    private ImmutableList<Goal> goals = ImmutableSLList.<Goal>nil();
    
    /** Create ProofTreeEvent for an event that happens at 
     * the specified node. */
    public ProofTreeEvent(Proof source,
			  Node  node) {
	this.source = source;
	this.node = node;
    }

    /** Create ProofTreeEvent for an event that happens at 
     * no particular node. */
    public ProofTreeEvent(Proof source) {
	this.source = source;
    }
    
    /** Create ProofTreeEvent for the event that happened to the 
     *	given goal
     */
    public ProofTreeEvent(Proof source, Goal goal) {
	this.source = source;
	this.goal = goal;
    }

    /** Create ProofTreeEvent for the event that affects the goals
     * given in the list.
     */
    public ProofTreeEvent(Proof source, ImmutableList<Goal> goals) {
	this.source = source;
	this.goals = goals;
    }

    public Node getNode() {
	return node;
    }

    public Proof getSource() {
	return source;
    }

    public Goal getGoal() {
	return goal;
    }

    public ImmutableList<Goal> getGoals() {
	return goals;
    }
    
    public String toString() {
        return "ProofTreeEvent: "+
            ( (node!=null) ? "node " : "" ) +
            ( (goal!=null) ? "goal " : "" ) +
            ( (!goals.isEmpty()) ? "goals " : "" );
    }
}