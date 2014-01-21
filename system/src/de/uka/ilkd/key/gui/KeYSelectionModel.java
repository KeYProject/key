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

package de.uka.ilkd.key.gui;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Debug;


public class KeYSelectionModel {

    /** the proof to listen to */
    private Proof proof;
    /** if true the selectedGoal field below can be trusted */
    private boolean goalIsValid;
    /** is the selected node a goal */
    private Goal selectedGoal;
    /** the current displayed node */
    private Node selectedNode;
    /** the listeners to this model */
    private List<KeYSelectionListener> listenerList;
    /** cached selected node event */
    private KeYSelectionEvent selectionEvent =
	new KeYSelectionEvent(this);

    KeYSelectionModel() {
	listenerList = Collections.synchronizedList(new ArrayList<KeYSelectionListener>(5));
	goalIsValid = false;
    }

    /** sets the selected proof
     * @param p the Proof that is selected
     */
    public void setSelectedProof(Proof p) {
	goalIsValid = false;
	proof = p;
        if (proof !=null) {
	    Goal g = proof.openGoals().iterator().next();
	    if ( g == null) {
	        selectedNode = proof.root().leavesIterator().next();
	    } else {
	        goalIsValid = true;
	        selectedNode = g.node();
	        selectedGoal = g;
	    }
        } else {
            selectedNode = null;
            selectedGoal = null;
        }
	fireSelectedProofChanged();
    }

    /** returns the proof that is selected by the user
     * @return  the proof that is selected by the user
     */
    public Proof getSelectedProof() {
	return proof;
    }

    /** sets the node that is focused by the user
     * @param n the selected node
     */
    public void setSelectedNode(Node n) {
	goalIsValid = false;
	selectedNode = n;
	fireSelectedNodeChanged();
    }

    /** sets the node that is focused by the user
     * @param g the Goal that contains the selected node
     */
    public void setSelectedGoal(Goal g) {
	goalIsValid = true;
	selectedGoal = g;
	selectedNode = g.node();
	fireSelectedNodeChanged();
    }

    /** returns the node that is selected by the user
     * @return  the node that is selected by the user
     */
    public Node getSelectedNode() {
	return selectedNode;
    }

    /** returns the goal the selected node belongs to, null if it is
     * an inner node
     * @return  the goal the selected node belongs to, null if it is
     * an inner node
     */
    public Goal getSelectedGoal() {
	if (proof==null) {
	    throw new IllegalStateException("No proof loaded.");
	}
	if (!goalIsValid) {
	    selectedGoal = proof.getGoal(selectedNode);
	    goalIsValid = true;
	}
	return selectedGoal;
    }

    /** returns true iff the selected node is a goal
     * @return true iff the selected node is a goal
     */
    public boolean isGoal() {
	if (!goalIsValid) {
	    return (getSelectedGoal() != null);
	}
	return selectedGoal != null;
    }


    /** enumerate the possible goal selections, starting with the best
     * one
     */
    protected class DefaultSelectionIterator implements Iterator<Goal> {
	private static final int POS_START     = 0;
	private static final int POS_LEAVES    = 1;
	private static final int POS_GOAL_LIST = 2;

	private int            currentPos = POS_START;
	private Goal           nextOne;
	private Iterator<Goal> goalIt;
	private Iterator<Node> nodeIt;

	public  DefaultSelectionIterator () {
	    findNext ();
	}

	private void findNext            () {
	    nextOne = null;
	    while ( nextOne == null ) {
		switch ( currentPos ) {
		case POS_START:
		    currentPos = POS_LEAVES;
		    if ( selectedNode != null )
			nodeIt = selectedNode.leavesIterator ();
		    else
			nodeIt = null;
		    break;
		case POS_LEAVES:
		    if ( nodeIt == null || !nodeIt.hasNext () ) {
			currentPos = POS_GOAL_LIST;
			if ( !proof.openGoals().isEmpty() )
			    goalIt = proof.openGoals().iterator();
			else
			    goalIt = null;
		    } else
			nextOne = proof.getGoal ( nodeIt.next() );
		    break;

		case POS_GOAL_LIST:
		    if ( goalIt == null || !goalIt.hasNext () )
			// no more items
			return;
		    else
			nextOne = goalIt.next();
		    break;
		}
	    }
	}

	public  Goal    next             () {
	    Goal res = nextOne;
	    findNext ();
	    return res;
	}

	public  boolean hasNext          () {
	    return nextOne != null;
	}

	public void remove() {
	    throw new UnsupportedOperationException();
	}
    }


    /**
     * Selects the goal in the goal list that is closest to the currently
     * selected node.
     * 
     * For a closed proof, it selects the root.
     * 
     * @see #nearestOpenGoalSelection(Node)
     */
    public void defaultSelection() {
        nearestOpenGoalSelection(getSelectedNode());
    }

    /**
     * Selects the goal in the goal list that is closest to the node {@code old}.
     * 
     * For a closed proof, it selects the root.
     * 
     * The goal with the shortest distance to old is selected.
     * 
     * If there are goals under old, search is restricted to those.
     * 
     * @param old
     *            the Node to start looking for open goals, not
     *            <code>null</code>
     */
    public void nearestOpenGoalSelection(Node old) {
        
        Set<Node> visited = 
                Collections.newSetFromMap(new IdentityHashMap<Node, Boolean>());
        
        Queue<Node> toVisit =
                new LinkedList<Node>();
        
        toVisit.add(old);
        
        if(!old.isClosed()) {
            // prevent going up in the tree by marking the parent as visited
            Node p = old.parent();
            if(p != null) {
                visited.add(p);
            }
        }

        // Now add all reachable nodes. Since the list toVisit is a queue, the
        // first found goal is the one with the shortest distance to old. This
        // is essentially a breadth-first-search.

        while(!toVisit.isEmpty()) {
            Node n = toVisit.remove();
            
            Node p = n.parent();
            if(p != null) {
                toVisit.add(p);
            }

            if(n.isClosed() || visited.contains(n)) {
                continue;
            }

            int childCount = n.childrenCount();
            if(childCount == 0) {
                // it is indeed a goal -> set it
                Goal goal = proof.getGoal(n);
                assert goal != null : "There must be a goal for this node";
                setSelectedGoal(goal);
                return;
            }

            for (int i = 0; i < childCount; i++) {
                toVisit.add(n.child(i));
            }

            visited.add(n);
        }

        // now no goal found
        Node root = proof.root();
        assert root.isClosed();
        setSelectedNode(root);
    }

    public void addKeYSelectionListener(KeYSelectionListener listener) {
	synchronized(listenerList) {
	    Debug.log4jInfo("Adding "+listener.getClass(), "key.threading");
	    listenerList.add(listener);
	}
    }

    public void removeKeYSelectionListener(KeYSelectionListener listener) {
	synchronized(listenerList) {
	    Debug.log4jInfo("Removing "+listener.getClass(), "key.threading");
	    listenerList.remove(listener);
	}
    }

    public synchronized void fireSelectedNodeChanged() {
	synchronized(listenerList) {
            for (final KeYSelectionListener listener : listenerList) {
                listener.selectedNodeChanged(selectionEvent);
	    }
	}
    }

    public synchronized void fireSelectedProofChanged() {
	synchronized(listenerList) {
	    Debug.log4jInfo("Selected Proof changed, firing...", "key.threading");
            for (final KeYSelectionListener listener : listenerList) {
	        listener.selectedProofChanged(selectionEvent);
	    }
            Debug.log4jInfo("Selected Proof changed, done firing.", "key.threading");
	}
    }

}
