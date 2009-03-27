// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.incclosure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.ConstraintContainer;
import de.uka.ilkd.key.logic.IntersectionConstraint;
import de.uka.ilkd.key.logic.op.Metavariable;


/**
 * Class for merging two constraint streams
 */
public class BinaryMerger implements Merger {

    private MergerSink leftSink  = new MergerSink ();
    private MergerSink rightSink = new MergerSink ();

    /**
     * Parent sink within the tree of sinks
     */
    private Sink       parent;

    /**
     * Services eg. if necessary additional sorts are added
     * (this can happen during unification)
     */
    private Services services;
    
    /**
     * Initial value of the buffers will be the parent's value
     */
    public BinaryMerger ( Sink p_parent, Services p_services ) {
	parent              = p_parent;

	leftSink .otherSink = rightSink;
	rightSink.otherSink = leftSink;

	leftSink .buffer    = parent.getResetConstraint ();
	rightSink.buffer    = parent.getResetConstraint ();
        
        services = p_services;
    }

    /**
     * Inputs offered by this merger
     */
    public IteratorOfSink getSinks () {
	return
	    SLListOfSink.EMPTY_LIST
	    .prepend ( rightSink )
	    .prepend ( leftSink )
	    .iterator ();
    }

    /**
     * Reparent this merger; an implementing class should make
     * appropriate "reset"-calls to the new parent
     */
    public void           setParent     ( Sink p_parent ) {
	parent = p_parent;
	parent.reset ( leftSink.buffer.join ( rightSink.buffer, 
                services ) );
    }

    /**
     * @return true iff the whole subtree of sinks below this merger
     * has seen consistent constraints
     */
    public boolean        isSatisfiable () {        
	return leftSink.buffer.join ( rightSink.buffer, 
                services ).isSatisfiable ();
    }

    private class MergerSink implements Sink {

	public MergerSink otherSink;

	public Constraint buffer;

	/**
	 * Add a constraint for which something (a goal or a subtree of
	 * the proof) can be closed
	 * computes a constraint representing the intersection of all
	 * constraints that have been pushed until now (including "p_c")
	 */
	public void       put                ( Constraint p_c ) {
	    if ( p_c.isSatisfiable () ) {
		ConstraintContainer cc = new ConstraintContainer ();
		buffer = IntersectionConstraint.intersect ( buffer, p_c, cc );
		p_c    = cc.val ().join ( otherSink.buffer, 
                        services );

		if ( p_c.isSatisfiable () )
		    parent.put ( p_c );
	    }
	}

	/**
	 * Tell the first restricter (possibly this sink) to remove "p_mv"
	 * from any passing constraint
	 *
	 * Restrictions should not leave its branches
	 */
	public void       addRestriction     ( Metavariable p_mv ) {
	    parent.addRestriction(p_mv);
        }

	/**
	 * @return a constraint that restores the current state of this
	 * sink and its parents if used with "reset"
	 */
	public Constraint getResetConstraint () {
	    return buffer;
	}

	/**
	 * Remove all constraints that have been inserted with "put" until
	 * now, replacing them with the only constraint "p_c"
	 */
	public void       reset ( Constraint p_c ) {
	    buffer = p_c;
	    parent.reset ( buffer.join ( otherSink.buffer, 
                    services ) );
	}

    }

}
