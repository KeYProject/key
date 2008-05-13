//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;

/**
 * Matching triggers within another quantifier expression. Problems with the
 * current implementation:
 * 
 * * the usage of EqualityConstraint for unification implies that a variable is
 * never instantiated with non-rigid terms
 * 
 * * it is unclear whether certain instantiations are lost due to too strict type
 * checks in EqualityConstraint
 */
class TwoSidedMatching {
	    
    private final UniTrigger trigger;
    private final Term triggerWithMVs;
    private final Substitution targetSubstWithMVs;
    private final Substitution triggerSubstWithMVs;
    private final Term targetWithMVs;
    
    TwoSidedMatching(UniTrigger trigger, Term targetTerm) {
        this.trigger = trigger;
        this.targetSubstWithMVs =
            ReplacerOfQuanVariablesWithMetavariables.createSubstitutionForVars ( targetTerm );
        this.triggerSubstWithMVs =
            trigger.getTriggerSetThisBelongsTo().getReplacementWithMVs ();
        this.targetWithMVs =
            targetSubstWithMVs.apply ( TriggerUtils.discardQuantifiers ( targetTerm ) );
        this.triggerWithMVs =
            triggerSubstWithMVs.apply ( trigger.getTriggerTerm () );
    }
    
    SetOfSubstitution getSubstitutions(Services services) {
        return getAllSubstitutions ( targetWithMVs, services );
    }
    
    private SetOfSubstitution getAllSubstitutions(Term target, Services services) {
        SetOfSubstitution allsubs = SetAsListOfSubstitution.EMPTY_SET;
        Substitution sub = match ( triggerWithMVs, target, services );
        if ( sub != null
             && ( trigger.isElementOfMultitrigger() || sub.isTotalOn ( trigger.getUniVariables() )
             // sub.containFreevar(trigger.ts.allTerm.
             // varsBoundHere(0).getQuantifiableVariable(0))
             ) ) {
            allsubs = allsubs.add ( sub );
        }
        final Operator op = target.op ();
        if ( !( op instanceof Modality || op instanceof IUpdateOperator ) ) {
            for ( int i = 0; i < target.arity (); i++ ) {
                allsubs = allsubs.union ( getAllSubstitutions ( target.sub ( i ), services ) );
            }
        }
        return allsubs;
    }
    
    /** find a substitution in a allterm by using unification */
    private Substitution match(Term triggerTerm, Term targetTerm, 
            Services services) {
        final Constraint c =
            Constraint.BOTTOM.unify ( targetTerm, triggerTerm,
                                      services );
        if ( c.isSatisfiable () ) {
            MapFromQuantifiableVariableToTerm sub =
                MapAsListFromQuantifiableVariableToTerm.EMPTY_MAP;
            IteratorOfQuantifiableVariable it = trigger.getUniVariables().iterator ();
            while ( it.hasNext () ) {
                QuantifiableVariable q = it.next ();
                Term mv = triggerSubstWithMVs.getSubstitutedTerm ( q );
                Term t = c.getInstantiation ( (Metavariable)( mv.op () ) );
                if ( t == null || t.op () instanceof Metavariable )
                    return null;
                if ( isGround ( t ) )
                    sub = sub.put ( q, t );
            }
            if ( sub.size () > 0 ) return new Substitution ( sub );
        }
        return null;
    }

    private boolean isGround(Term t) {
        return !triggerSubstWithMVs.termContainsValue ( t )
               && !targetSubstWithMVs.termContainsValue ( t );
    } 
}