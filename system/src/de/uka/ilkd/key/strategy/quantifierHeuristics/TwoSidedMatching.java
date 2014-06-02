// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.DefaultImmutableMap;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
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
    
    TwoSidedMatching(UniTrigger trigger, Term targetTerm, TermServices services) {
        this.trigger = trigger;
        this.targetSubstWithMVs =
            ReplacerOfQuanVariablesWithMetavariables.createSubstitutionForVars ( targetTerm, services );
        this.triggerSubstWithMVs =
            trigger.getTriggerSetThisBelongsTo().getReplacementWithMVs ();
        
        if (targetSubstWithMVs.isGround()) {
            this.targetWithMVs =
            targetSubstWithMVs.apply ( TriggerUtils.discardQuantifiers ( targetTerm ), services );
        } else {
            this.targetWithMVs = null;            
        }
        if (triggerSubstWithMVs.isGround()) {
            this.triggerWithMVs =
            triggerSubstWithMVs.apply ( trigger.getTriggerTerm (), services );
        } else {
            this.triggerWithMVs = null;            
        }
    }
    
    ImmutableSet<Substitution> getSubstitutions(TermServices services) {
        if (triggerWithMVs == null || targetWithMVs == null) {
            // non ground subs not supported yet
            return DefaultImmutableSet.<Substitution>nil();
        }
	return getAllSubstitutions ( targetWithMVs, services );
    }
    
    private ImmutableSet<Substitution> getAllSubstitutions(Term target, TermServices services) {
        ImmutableSet<Substitution> allsubs = DefaultImmutableSet.<Substitution>nil();
        Substitution sub = match ( triggerWithMVs, target, services );
        if ( sub != null
             && ( trigger.isElementOfMultitrigger() || sub.isTotalOn ( trigger.getUniVariables() )
             // sub.containFreevar(trigger.ts.allTerm.
             // varsBoundHere(0).getQuantifiableVariable(0))
             ) ) {
            allsubs = allsubs.add ( sub );
        }
        final Operator op = target.op ();
        if ( !( op instanceof Modality || op instanceof UpdateApplication ) ) {
            for ( int i = 0; i < target.arity (); i++ ) {
                allsubs = allsubs.union ( getAllSubstitutions ( target.sub ( i ), services ) );
            }
        }
        return allsubs;
    }
    
    /** find a substitution in a allterm by using unification */
    private Substitution match(Term triggerTerm, Term targetTerm, 
            TermServices services) {
        final Constraint c =
            Constraint.BOTTOM.unify ( targetTerm, triggerTerm,
                                      services );
        if ( c.isSatisfiable () ) {
            ImmutableMap<QuantifiableVariable,Term> sub =
                DefaultImmutableMap.<QuantifiableVariable,Term>nilMap();
            for (QuantifiableVariable quantifiableVariable : trigger.getUniVariables()) {
                QuantifiableVariable q = quantifiableVariable;
                Term mv = triggerSubstWithMVs.getSubstitutedTerm(q);
                Term t = c.getInstantiation((Metavariable) (mv.op()), services);
                if (t == null || t.op() instanceof Metavariable)
                    return null;
                if (isGround(t))
                    sub = sub.put(q, t);
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