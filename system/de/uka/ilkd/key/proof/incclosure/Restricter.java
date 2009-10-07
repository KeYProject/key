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

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.op.Metavariable;


/**
 * Sink removing given metavariables from passing constraints, thus
 * making variables local
 */
public class Restricter implements Sink {

    /**
     * Variables to remove from passing constraints
     */
    private ImmutableSet<Metavariable> removedVariables =
	DefaultImmutableSet.<Metavariable>nil();

    /**
     * Parent sink within the tree of sinks
     */
    private Sink              parent;

    /**
     * PRECONDITION: p_parent != null
     */
    public Restricter ( Sink p_parent ) {
	parent = p_parent;
    }

    /**
     * Add a constraint for which something (a goal or a subtree of
     * the proof) can be closed
     */
    public void       put                ( Constraint p_c ) {
	if ( p_c.isSatisfiable () )
	    parent.put ( p_c.removeVariables ( removedVariables ) );
    }

    /**
     * Tell the first restricter (possibly this sink) to remove "p_mv"
     * from any passing constraint
     */
    public void       addRestriction     ( Metavariable p_mv ) {
	removedVariables = removedVariables.add ( p_mv );
        // also pass the restriction upwards, because the removed variables
        // might still occur as right-hand side (and might reoccur later for
        // this reason)
        parent.addRestriction(p_mv);
    }

    public ImmutableSet<Metavariable> getRestrictions () {
	return removedVariables;
    }

    /**
     * @return a constraint that restores the current state of this
     * sink and its parents if used with "reset"
     */
    public Constraint getResetConstraint () {
	return parent.getResetConstraint ();
    }

    /**
     * Remove all constraints that have been inserted with "put" until
     * now, replacing them with the only constraint "p_c"
     */
    public void       reset              ( Constraint p_c ) {
	// The set of removed variables is currently not resetted
	parent.reset ( p_c );
    }

    protected Sink    getParent          () {
	return parent;
    }

}
