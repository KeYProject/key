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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.rule.UpdateSimplifier;

/**
 * An abstract update simplification rule for application on array access
 * operators.
 * 
 * @author bubel
 */
public class ApplyOnArrayAccess extends ApplyOnAccessTerm {

    /**
     * @param updateSimplifier
     */
    public ApplyOnArrayAccess(UpdateSimplifier updateSimplifier) {
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
        return target.op () instanceof ArrayOp;
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
               
        if (!(result.sort().extendsTrans(target.sort()))) {
            return UpdateSimplifierTermFactory.DEFAULT.
            getBasicTermFactory().createCastTerm((AbstractSort)target.sort(), result);
        }
        return result;
        
    }
    
    private ArrayIfExCascade createCascade (PropagationResult pr,
                                            Update update,
                                            Term target) {
        return new ArrayIfExCascade ( update.getAssignmentPairs ( (Location)target.op () ),
                                      new ArrayOfTerm ( pr.getSimplifiedSubterms () ),
                                      (Location)target.op () );
    } 

    private Term updateSubterms (PropagationResult pr, Term target) {
        if ( !pr.hasChanged () ) return target;

        final TermFactory tf =
            UpdateSimplifierTermFactory.DEFAULT.getBasicTermFactory ();

        return tf.createArrayTerm ( (ArrayOp)target.op (),
                                    pr.getSimplifiedSubterms () );
    }

    private static class ArrayIfExCascade extends
                               IterateAssignmentPairsIfExCascade {

        private final Location                  targetLoc;
        private final ArrayOfTerm               targetSubs;
        private final SetOfQuantifiableVariable criticalVars;

        public ArrayIfExCascade (ArrayOfAssignmentPair pairs,
                                 ArrayOfTerm targetSubs,
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
            final Term eqObjects =
                compareObjects ( targetSubs.getTerm ( 0 ),
                                 getCurrentPair ().locationSubs ()[0] );
            final Term eqIndex =
                tf.createEqualityTerm ( targetSubs.getTerm ( 1 ),
                                        getCurrentPair ().locationSubs ()[1] );
            res = tf.createJunctorTermAndSimplify ( Op.AND, res, eqObjects );
            res = tf.createJunctorTermAndSimplify ( Op.AND, res, eqIndex );

            if ( targetLoc instanceof ShadowedOperator
                 && getCurrentPair ().location () instanceof ShadowedOperator ) {
                // in this case a conjunction of conditions has to be used
                // as the transaction number needs to be checked as well  
                final Term eqTrans =
                    tf.createEqualityTerm ( targetSubs.getTerm ( 2 ),
                                            getCurrentPair ().locationSubs ()[2] );
                res = tf.createJunctorTermAndSimplify ( Op.AND, res, eqTrans );
            }

            return res;
        }
        
        protected SetOfQuantifiableVariable criticalVars () {
            return criticalVars;
        }
    }

    public Term matchingCondition (Update update, Term target, Services services) {
        // the field reference part (and if shadowed the transaction number)
        // of target evaluated in the state described by the update
        final PropagationResult pr = propagateUpdateToSubterms ( update, target, services );
        
        return UpdateSimplifierTermFactory.DEFAULT
            .matchingCondition ( createCascade ( pr, update, target ) );
    }
}
