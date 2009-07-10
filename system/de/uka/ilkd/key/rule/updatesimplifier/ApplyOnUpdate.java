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
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.OldUpdateSimplifier;
import de.uka.ilkd.key.util.Debug;


/**
 * Applies an update on an array using rule ...
 */
public class ApplyOnUpdate extends AbstractUpdateRule {
          
    /**
     * creates an instance of this rule used by the given update
     * simplifier
     */
    public ApplyOnUpdate(OldUpdateSimplifier us) {
        super(us);
    }

    /**
     * determines whether this rule is applicable for the 
     * update x target (the term on which the update will be
     * applied) pair 
     * @param update the Update to be applied on target
     * @param target the Term on which the update is applied
     * @return true if the top level operator of target is an
     * attribute operator
     */
    public boolean isApplicable(Update update, Term target) {
	return target.op() instanceof IUpdateOperator;
    }

    /**
     * determines whether this rule is applicable for the pair of update and
     * target (the term on which the update will be applied) term
     * 
     * @param update
     *            the Update to be applied on the given term
     * @param target
     *            the Term on which the update is applied
     * @param services
     *            the Services object
     * @return true if the rule can be applied on the update, target pair
     */
    public Term apply (Update update, Term target, Services services) {
        final UpdateFactory ufac = new UpdateFactory(services, 
                                                     updateSimplifier());
        final Update targetUpdate = Update.createUpdate ( target );
        final Update composedUpdate = ufac.sequential ( update, targetUpdate );
        final IUpdateOperator updateOp = (IUpdateOperator)target.op ();
        final Term subTarget = updateOp.target ( target );
        return ufac.apply ( composedUpdate, subTarget );
    }
        
    public Term matchingCondition (Update update, 
	    			   Term target, 
	    			   Services services) {
        // an update is not a location
        Debug.fail ( "matchingCondition(...) must not be called for target "
                     + target );
        return null; // unreachable
    }
}
