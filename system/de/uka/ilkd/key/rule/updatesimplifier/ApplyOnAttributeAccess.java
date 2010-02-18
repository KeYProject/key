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
 * Created on 18.12.2004
 */
package de.uka.ilkd.key.rule.updatesimplifier;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.UpdateSimplifier;

/**
 * An abstract update simplification rule for update application on attribute 
 * access terms. This class is inherited by the concrete ruels for shadowed 
 * and unshadowed attribute accesses.
 * 
 * @author bubel
 */
public class ApplyOnAttributeAccess extends ApplyOnAccessTerm {
    
    /**
     * 
     * @param updateSimplifier 
     */
    public ApplyOnAttributeAccess(UpdateSimplifier updateSimplifier) {
        super(updateSimplifier);
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
    public boolean isApplicable (Update update, Term target) {
        return (target.op () instanceof AttributeOp)
                || 
                (target.op() instanceof NonRigidFunctionLocation && 
                        target.op().arity() > 0);
    }    

    /**
     * applies an update on a term representing an instance attribute
     * 
     * @param update
     *            the Update to be applied on target
     * @param target
     *            the Term representing an instance attribute
     * @param services
     *            the Services object
     * @return the simplified term describing the value of target under the
     *         given update
     * @requires update != null && target!=null && target.op() instanceof
     *           AttributeOp && !(target.op() instanceof ShadowedOperator)
     */
    public Term apply(Update update, Term target, Services services) {
        logEnter(update, target);

        // the field reference part (and if shadowed the transaction number)
        // of target evaluated in the state described by the update
        final PropagationResult pr = propagateUpdateToSubterms ( update, 
        	                                                 target, 
        	                                                 services );
        
        final Term result = UpdateSimplifierTermFactory.DEFAULT
            .createIfExCascade ( createCascade ( pr, update, target ),
                                 updateSubterms ( pr, target ) );

        logExit(result);
        
        return result;
    }

    
    private AttrIfExCascade createCascade (PropagationResult pr,
                                           Update update,
                                           Term target) {
        return new AttrIfExCascade ( update.getAssignmentPairs ( (Location)target.op () ),
                                     new ImmutableArray<Term> ( pr.getSimplifiedSubterms () ),
                                     (Location)target.op () );
    }

    private Term updateSubterms (PropagationResult pr, Term target) {
        if ( !pr.hasChanged () ) return target;

        final TermFactory tf =
            UpdateSimplifierTermFactory.DEFAULT.getBasicTermFactory ();
        return target.op() instanceof AttributeOp ? 
                tf.createAttributeTerm ( (AttributeOp)target.op (),
                                        pr.getSimplifiedSubterms () ) :
                                            tf.createFunctionTerm((Function)target.op(), 
                                                    pr.getSimplifiedSubterms());
    }   

    private static class AttrIfExCascade
                                extends IterateAssignmentPairsIfExCascade {
        
        private final Location targetLoc;
        private final ImmutableArray<Term> targetSubs;
        private final ImmutableSet<QuantifiableVariable> criticalVars;
        
        public AttrIfExCascade (ImmutableArray<AssignmentPair> pairs,
                                ImmutableArray<Term> targetSubs,
                                Location targetLoc) {
            super ( pairs );
            this.targetSubs = targetSubs;
            this.targetLoc = targetLoc;
            this.criticalVars = freeVars ( targetSubs );
        }
        
        public Term getCondition () {
            final TermFactory tf =
                UpdateSimplifierTermFactory.DEFAULT.getBasicTermFactory ();

            Term res = getCurrentPair ().guard ();
            
            assert (targetLoc instanceof ShadowedOperator &&
		    getCurrentPair().location() instanceof AttributeOp)
		||targetSubs.size() == getCurrentPair().locationSubs().length;

            for (int i = 0, arity = targetSubs.size(); i < arity; i++) {
//              attention we need not to take care of 
                // the case {o.a':=t}o.a --> o.a as in this case this method must not 
                // be called (hint:update.getAssignmentPairs ( (Location)target.op () )
                // returns only possible aliased assignement pairs)
                if ( !(targetLoc instanceof ShadowedOperator) ||
                    getCurrentPair().location() instanceof ShadowedOperator || i != 1) {               
                    final Term eqObjects =
                        compareObjects ( targetSubs.get ( i ),
                                getCurrentPair ().locationSubs ()[i] );
                    res = tf.createJunctorTermAndSimplify ( Op.AND, res, eqObjects );
                }
            }
                
            
            
            
            return res;
        }

        protected ImmutableSet<QuantifiableVariable> criticalVars () {
            return criticalVars;
        }
    }

    public Term matchingCondition (Update update, 
	    			   Term target, 
	    			   Services services) {
        // the field reference part (and if shadowed the transaction number)
        // of target evaluated in the state described by the update
        final PropagationResult pr = propagateUpdateToSubterms ( update, 
        						         target, 
        						         services );
        
        return UpdateSimplifierTermFactory.DEFAULT
            .matchingCondition ( createCascade ( pr, update, target ) );
    }
}
