// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.incclosure;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.ConstraintContainer;
import de.uka.ilkd.key.logic.IntersectionConstraint;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Debug;


/**
 * Sink removing given metavariables from passing constraints, thus
 * making variables local
 *
 * This derivative does also detect subtrees which are completely
 * closed
 */
public class BranchRestricter extends Restricter {

    Node       node           = null;

    /**
     * Constraint holding the intersection of all branch constraints
     * (constraints held by the branch sinks) above and at this
     * restricter's node
     * this is undefined if node == null
     */
    Constraint pathConstraint = Constraint.TOP;

    /**
     * PRECONDITION: p_parent != null
     */
    public BranchRestricter ( Sink p_parent ) {
	super ( p_parent );
    }

    /*
     * @param p_node the root of the branch (subtree) this restricter
     * belongs to
     */
    public void       setNode             ( Node       p_node ) {
	node = p_node;

	resetPathConstraint ();
    }

    /**
     * Add a constraint for which something (a goal or a subtree of
     * the proof) can be closed
     */
    public void       put                 ( Constraint p_c ) {
	super.put ( p_c );

	if ( node != null ) {
	    if ( getParent ().getResetConstraint ().isBottom () )
		node.subtreeCompletelyClosed ();

	    putPathConstraint ( getParent ().getResetConstraint () );
	}
    }

    /**
     * Remove all constraints that have been inserted with "put" until
     * now, replacing them with the only constraint "p_c"
     */
    public void       reset               ( Constraint p_c ) {
        pathConstraint = null;

        super.reset ( p_c );

        if ( pathConstraint == null )
            // otherwise the constraint was already reset by a recursive call
            resetPathConstraint ();
    }

    /**
     * Set the "pathConstraint"-attribute to the intersection of all
     * branch constraints (constraints held by the branch sinks) above
     * and at this restricter's node, propagate this change downwards
     *
     * PRECONDITION: the "pathConstraint"-attributes above this node
     * are up to date
     */
    protected void    resetPathConstraint () {
	Debug.assertTrue ( node != null,
			   "Branch restricter doesn't know its branch" );
	
	pathConstraint = Constraint.TOP;

	// go upwards to the next BranchRestricter, take its
	// pathConstraint
	Node n = node;
	while ( n.getBranchSink () == this && !n.root () )
	    n = n.parent ();

	if ( n.getBranchSink () != this ) {
	    Sink sink = n.getBranchSink ();
	    if ( sink instanceof BranchRestricter )
		pathConstraint = ((BranchRestricter)sink).getPathConstraint ();
	}

	resetPathConstraint ( pathConstraint );
    }

    /**
     * Set the "pathConstraint"-attribute to the intersection of p_c
     * with the local branch constraint, propagate this change
     * downwards
     */
    protected void    resetPathConstraint ( Constraint p_c ) {
	pathConstraint = IntersectionConstraint.intersect
	    ( getParent ().getResetConstraint (), p_c );

	final Iterator<Node> it   = nextNodesBelow ();
	Sink           sink;

	while ( it.hasNext () ) {
	    sink = it.next ().getBranchSink ();
	    if ( sink instanceof BranchRestricter )
		((BranchRestricter)sink).resetPathConstraint ( pathConstraint );
	}
    }

    /**
     * Intersect the "pathConstraint"-attribute with p_c, propagate
     * this change downwards
     */
    protected void    putPathConstraint   ( Constraint p_c ) {
	ConstraintContainer cc = new ConstraintContainer ();

	pathConstraint = IntersectionConstraint.intersect ( pathConstraint,
							    p_c, cc );

	if ( cc.val ().isSatisfiable () ) {
	    final Iterator<Node> it   = nextNodesBelow ();
	    Sink           sink;

	    while ( it.hasNext () ) {
		sink = it.next ().getBranchSink ();
		if ( sink instanceof BranchRestricter )
		    ((BranchRestricter)sink).putPathConstraint ( cc.val () );
	    }
	}
    }

    /**
     * @return Constraint holding the intersection of all branch
     * constraints (constraints held by the branch sinks) above and at
     * this restricter's node
     */
    public Constraint getPathConstraint   () {
	return pathConstraint;
    }

    /**
     * From "node" go downwards within the proof tree to the next node
     * with more than one child, return an iterator of the children
     */
    private Iterator<Node> nextNodesBelow () {
	Node n;

	Debug.assertTrue ( node != null,
			   "Branch restricter doesn't know its branch" );

	n = node;
	while ( n.childrenCount () == 1 )
	    n = n.child ( 0 );

	return n.childrenIterator ();
    }

}
