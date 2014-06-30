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

package de.uka.ilkd.key.gui;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

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
    private final List<KeYSelectionListener> listenerList;
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


    /** selects the first goal in the goal list of proof if available
     * if not it selects a leaf of the proof tree
     */
    public void defaultSelection() {
	Goal           g       = null;
	Goal           firstG  = null;
	Iterator<Goal> it      = new DefaultSelectionIterator ();

	while ( g == null && it.hasNext () ) {
	    g = it.next ();
	    if ( firstG == null )
		firstG = g;
	}

	/** Order of preference:
	 * 1. Not yet closable goals
	 * 2. Goals which are not closed for all metavariable
	 * instantiations
	 * 3. The first node of the tree
	 */
	if ( g != null )
	    setSelectedGoal(g);
	else {
	    if ( firstG != null )
		setSelectedGoal(firstG);
	    else
		setSelectedNode(proof.root().leavesIterator().next());
	}
	/*
	if (selectedNode != null) {
	    Iterator<Node> nodeIt = selectedNode.leavesIterator();
	    while (nodeIt.hasNext()) {
		g = proof.getGoal(nodeIt.next());
		if (g != null) {
		    break;
		}
	    }
	}
	if (g == null && !proof.openGoals().isEmpty() ) {
	    g = proof.openGoals().iterator().next();
	}
	if (g != null) {
	    setSelectedGoal(g);
	} else {
	    setSelectedNode(proof.root().leavesIterator().next());
	}
	*/
    }

    /**
     * selects the first open goal below the given node <tt>old</tt>
     * if no open goal is available node <tt>old</tt> is selected. In case
     * that <tt>old</tt> has been removed from the proof the proof root is
     * selected
     * @param old the Node to start looking for open goals
     */
    // XXX this method is never used
    public void nearestOpenGoalSelection(Node old) {
        Node n = old;
        while (n!=null && n.isClosed()) {
            n = n.parent();
        }
        if (n == null) {
            if (proof.find(old)) {
                setSelectedNode(old);
            } else {
                setSelectedNode(proof.root());
            }
        } else {
            final Goal g = getFirstOpenGoalBelow(n);
            if (g == null || g.node() == null) {
                setSelectedNode(proof.root());
            } else {
                setSelectedGoal(g);
            }
	}
    }

    /**
     * retrieves the first open goal below the given node, i.e. the goal
     * containing the first leaf of the subtree starting at
     *  <code>n</code> which is not already closed
     *
     * @param n the Node where to start from
     * @return the goal containing the first leaf of the
     * subtree starting at <code>n</code>, which is not already closed.
     * <code>null</code> is returned if no such goal exists.
     */
    private Goal getFirstOpenGoalBelow(Node n) {
        final Iterator<Node> it = n.leavesIterator();
        while (it.hasNext()) {
            final Node node =it.next();
            if (!node.isClosed()) {
               return proof.getGoal(node);
            }
        }
        return null;
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
