// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
/*
 * Created on 15.12.2004
 */
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.UpdateSimplifier;

/**
 * Applies an anonymous update on a term with a non-rigid operator as top 
 * level symbol. The update is added in front of the terms and also recursively
 * applied on the subterms.
 */
public class ApplyAnonymousUpdateOnNonRigid extends AbstractUpdateRule {

    /**
     * @param updateSimplifier
     */
    public ApplyAnonymousUpdateOnNonRigid(UpdateSimplifier updateSimplifier) {
        super(updateSimplifier);      
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.UpdateRule#isApplicable(de.uka.ilkd.key.rule.updatesimplifier.Update, de.uka.ilkd.key.logic.Term)
     */
    public boolean isApplicable(Update update, Term target) {        
        final Operator op = target.op();
        return update.isAnonymousUpdate() && 
           op instanceof NonRigid && !(op instanceof AnonymousUpdate);
    }

    /**
     * in case of a non-state changing non rigid top level operator, the anonymous update is also 
     * propagated to the subterm
     * @param update the Update to be pushed
     * @param target the Term where to apply the anonymous update
     * @param services the Services
     * @return the term after pushing the update to the subterms
     */
    private Term pushToSubterms(Update update, Term target, Services services) {
	Term result = target;
	final PropagationResult pr = propagateUpdateToSubterms(update, 
							       target, 
							       services);        
	final Term[] subs = pr.getSimplifiedSubterms();
	final ArrayOfQuantifiableVariable[] vars = pr.getBoundVariables();
             
	if (pr.hasChanged()) {
	    result = UpdateSimplifierTermFactory.DEFAULT.getBasicTermFactory().
		createTerm(target.op(), subs, vars, target.javaBlock());           
	} else  {
	    result = target;
	}

	return result;
    }
    

    /**
     * applies the annonymous update on the target term
     */
    public Term apply(Update update, Term target, Services services) {
        // use update simplifier termfactory in particular to be sure to create correct 
        // anonymous updates
        logEnter(update, target);

	Term result = updateSimplifier().simplify(target, services);

	if ( result.op() != target.op() && !isApplicable(update, result) ) {
	    result = updateSimplifier().simplify(update, result, services);
	    logExit(result);
	    return result;
	}
	    
	// push to sub terms if no state changing operator
	if (!(result.op() instanceof Modality || 
	      result.op() instanceof IUpdateOperator)) {
	    result = pushToSubterms(update, result, services);
	} 

	// add anonymous update in front of the term

	result = UpdateSimplifierTermFactory.DEFAULT.
	    createUpdateTerm(update.getAllAssignmentPairs(), result);

	logExit(result);
	return result;
    }

    public Term matchingCondition (Update update, 
	    			   Term target, 
	    			   Services services) {
        // anonymous updates will always affect the value of a non-rigid symbol
        // ... really? /PR
        return UpdateSimplifierTermFactory.DEFAULT.getValidGuard ();
    }
}
