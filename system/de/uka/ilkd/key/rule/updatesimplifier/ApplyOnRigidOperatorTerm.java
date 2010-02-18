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
 * Created on 26.11.2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.op.NonRigid;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.AbstractUpdateRule;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.util.Debug;

/**
 * Applies an update on a term whose top level operator is 
 * a rigid operator. In fact, the update is and needs only be 
 * passed through to the subterms
 */
public class ApplyOnRigidOperatorTerm extends AbstractUpdateRule {

    /**
     * @param us the UpdateSimplifier this rule is registered at
     */
    public ApplyOnRigidOperatorTerm(UpdateSimplifier us) {
        super(us);   
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.rule.UpdateRule#isApplicable(de.uka.ilkd.key.rule.updatesimplifier.Update, de.uka.ilkd.key.logic.Term)
     */
    public boolean isApplicable(Update update, Term target) {        
        return !(target.op() instanceof NonRigid);
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.uka.ilkd.key.rule.UpdateRule#apply(de.uka.ilkd.key.rule.updatesimplifier.Update,
     *      de.uka.ilkd.key.logic.Term)
     */
    public Term apply(Update update, Term target, Services services) {
        final Term result;
                
        final PropagationResult pr = propagateUpdateToSubterms(update, 
        						       target, 
        						       services);        
        final Term[] subs = pr.getSimplifiedSubterms();
        final ImmutableArray<QuantifiableVariable>[] vars = pr.getBoundVariables();
             
        if (pr.hasChanged()) {
            result = UpdateSimplifierTermFactory.DEFAULT.getBasicTermFactory().
            createTerm(target.op(), subs, vars, target.javaBlock());           
        } else  {
            result = target;
        }
        
        return result;
    }
    
    public Term matchingCondition (Update update, 
	    			   Term target, 
	    			   Services services) {
        // these rigid operators should not be locations,
        // otherwise something is very wrong
        Debug.assertFalse ( target.op () instanceof Location, "Rewrite me!" );
        Debug.fail ( "matchingCondition(...) must not be called for target "
                     + target );
        return null; // unreachable
    }
}
