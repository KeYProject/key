// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.util.Debug;

/**
 * Models an assignment pair <code> l_i := t_i </code>  of an update.
 * This data structure is only used for update simplification.
 */
public class AssignmentPairLazy extends AbstractAssignmentPairLazy {
    
    /**
     * creates the assignment pair <code> l_i := t_i </code>
     * @param update the Term with update as top level operator whose
     * locationPos-th assignment pair is modeled 
     * @param locationPos the position of the location of this assignment pair
     */
    public AssignmentPairLazy(Term update, int locationPos) {
        super(update, locationPos);
        Debug.assertTrue ( getUpdateOp () instanceof AnonymousUpdate );
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#boundVars()
     */
    public ArrayOfQuantifiableVariable boundVars () {
        return new ArrayOfQuantifiableVariable ();
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#guard()
     */
    public Term guard () {
        return UpdateSimplifierTermFactory.DEFAULT.getValidGuard ();
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair#nontrivialGuard()
     */
    public boolean nontrivialGuard () {
        return false;
    }
}
