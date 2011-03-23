// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.incclosure;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.IntersectionConstraint;
import de.uka.ilkd.key.logic.op.Metavariable;


/**
 * Sink buffering all constraints that are pushed using "put",
 * offering the possibility to reset the tree of sinks
 */
public class BufferSink implements Sink {

    private Constraint buffer;

    /**
     * Parent sink within the tree of sinks. For "parent == null" this
     * is the root sink
     */
    private Sink       parent;
    
    
    /**
     * Initial value of the buffer will be the parent's value
     */
    public BufferSink ( Sink p_parent ) {
	parent = p_parent;
	
        if ( parent == null )
	    buffer = Constraint.TOP;
	else
	    buffer = parent.getResetConstraint ();               
    }

    /**
     * @return the buffered constraint
     */
    public Constraint getConstraint      () {
	return buffer;
    }

    public boolean    isSatisfiable      () {
	return buffer.isSatisfiable ();
    }

    /**
     * Add a constraint for which something (a goal or a subtree of
     * the proof) can be closed
     */
    public void       put                ( Constraint p_c ) {
	if ( p_c.isSatisfiable () ) {
	    if ( parent == null )
		buffer = IntersectionConstraint.intersect ( buffer, p_c );
	    else {
		parent.put ( p_c );
		buffer = parent.getResetConstraint ();
	    }
	}
    }

    /**
     * Tell the first restricter (possibly this sink) to remove "p_mv"
     * from any passing constraint
     */
    public void       addRestriction     ( Metavariable p_mv ) {
	if ( parent != null )
	    parent.addRestriction ( p_mv );
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
	if ( parent != null )
	    parent.reset ( p_c );
    }

    public void       reset () {
	reset ( buffer );
    }

}
