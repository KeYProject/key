// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.proofevent;


import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.RuleApp;


/**
 * Collect changes applied to a node during a given period of time
 */
public class NodeChangeJournal implements GoalListener {

    private final Proof proof;

    /**
     * The original node
     */
    private final Node  node;

    /**
     * This is a may storing the leaves that are currently below
     * the original node, and all changes applied to each of them
     */
    private MapFromNodeToNodeChangesHolder changes =
	MapAsListFromNodeToNodeChangesHolder.EMPTY_MAP;

    /**
     * @param p_goal the original goal/node
     */
    public NodeChangeJournal ( Proof p_proof,
			       Goal  p_goal ) {
	proof = p_proof;
	node  = p_goal.node ();
        putChangeObj(node, new NodeChangesHolder ());
    }


    /**
     * Create an RuleAppInfo object containing all changes stored
     * within this object; remove all listeners
     */
    public RuleAppInfo getRuleAppInfo ( RuleApp p_ruleApp ) {
	IteratorOfEntryOfNodeAndNodeChangesHolder it  = changeObjIterator ();
	ListOfNodeReplacement                     nrs =
	    SLListOfNodeReplacement.EMPTY_LIST;

	while ( it.hasNext () ) {
	    final EntryOfNodeAndNodeChangesHolder entry = it.next ();
	    final Node newNode = entry.key ();
	    final Goal newGoal = proof.getGoal ( newNode );

	    if ( newGoal != null ) {
		final NodeChangesHolder nc = entry.value ();

		nrs = nrs.prepend ( new NodeReplacement
				    ( newNode, node, nc.scis ) );
	    
		newGoal.removeGoalListener ( this );
	    }
	}

	return new RuleAppInfo ( p_ruleApp, node, nrs );
    }


    // GoalListener methods

    /** 
     * informs the listener about a change that occured to the sequent
     * of goal
     */
    public void sequentChanged ( Goal              source,
				 SequentChangeInfo sci ) {
        NodeChangesHolder nc = getChangeObj(source.node ());
        
	if ( nc != null )
	    nc.addSCI ( sci );
    }


    /**
     * Informs the listener that the given goal <code>source</code>
     * has been replaced by the goals <code>newGoals</code> (note that
     * <code>source</code> may be an element of
     * <code>newGoals</code>). The nodes of <code>newGoals</code> are
     * children of the node <code>parent</code>
     */
    public void goalReplaced(Goal source, Node parent, ListOfGoal newGoals) {
	NodeChangesHolder nc = removeChangeObj(parent);

	if ( nc != null ) {
	    IteratorOfGoal it = newGoals.iterator ();
	    if ( it.hasNext () ) {
		while ( true ) {
		    putChangeObj ( it.next ().node (), nc );
		    if ( !it.hasNext () )
			break;
		    nc = (NodeChangesHolder)nc.clone ();
		}
	    }
	}
    }


    private void putChangeObj(Node p_node, NodeChangesHolder p_obj) {
	changes = changes.put ( p_node, p_obj );
    }

    private NodeChangesHolder getChangeObj(Node p_node) {
	return changes.get ( p_node );
    }

    private NodeChangesHolder removeChangeObj(Node p_node) {
	final NodeChangesHolder res = changes.get ( p_node );
	changes = changes.remove ( p_node );
        return res;
    }

    private IteratorOfEntryOfNodeAndNodeChangesHolder changeObjIterator () {
	return changes.entryIterator ();
    }


}
