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

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.op.Metavariable;


/**
 * Interface for the closure constraint consuming classes
 */
public interface Sink {

    /**
     * Add a constraint for which something (a goal or a subtree of
     * the proof) can be closed
     */
    void       put                ( Constraint   p_c );

    /**
     * Tell the first restricter (possibly this sink) to remove "p_mv"
     * from any passing constraint
     */
    void       addRestriction     ( Metavariable p_mv );

    /**
     * @return a constraint that restores the current state of this
     * sink and its parents if used with "reset"
     */
    Constraint getResetConstraint ();

    /**
     * Remove all constraints that have been inserted with "put" until
     * now, replacing them with the only constraint "p_c"
     */
    void       reset              ( Constraint   p_c );

}
