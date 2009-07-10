// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.OldUpdateSimplifier;
import de.uka.ilkd.key.util.Debug;

/**
 * Rule used by the update simplifier as application of an update on
 * a rigid function or variable.
 * Implements rule (...) described in ....
 */
public class ApplyOnRigidTerm extends AbstractUpdateRule {

    /**
     * creates an instance of this rule used by the given update
     * simplifier
     */
    public ApplyOnRigidTerm(OldUpdateSimplifier us) {
	super(us);
    }

    /**
     * determines whether this rule is applicable for the pair of
     * update and target (the term on which the update will be
     * applied) term. 
     * @param update the Update to be applied on target
     * @param target the Term on which the update is applied
     * @return true if the top level operator of target is a local
     * variable
     */
    public boolean isApplicable(Update update, Term target) {	
	return target.isRigid();
    }

    public Term apply(Update update, Term target, Services services) {	
	return target;
    }
    
    public Term matchingCondition (Update update, 
	    			   Term target, 
	    			   Services services) {
        // these rigid operators should not be locations,
        // otherwise something is very wrong
        Debug.assertFalse ( target.op () instanceof UpdateableOperator, "Rewrite me!" );
        Debug.fail ( "matchingCondition(...) must not be called for target "
                     + target );
        return null; // unreachable
    }
}
