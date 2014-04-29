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

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.FormulaTag;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;


/**
 * A rule app manager that ensures that rules are only applied to a certain
 * subterm within the proof (within a goal). The real work is delegated to a
 * second manager (delegate pattern), this class only filters rule applications
 */
public class FocussedRuleApplicationManager implements AutomatedRuleApplicationManager {

    private final AutomatedRuleApplicationManager delegate;

    private final FormulaTag              focussedFormula;
    private final PosInOccurrence         focussedSubterm;

    private Goal                          goal;
    
    // Until <code>next</code> was called for the first time only rule
    // applications for the focussed formula are accepted, after that also
    // applications for other formulas. The idea is that then the rule index
    // caches are filled and further reported rules involve modified or new
    // formulas (this works at least for delegate
    // <code>QueueRuleApplicationManager</code>)
    private boolean                       onlyModifyFocussedFormula;
    
    private FocussedRuleApplicationManager (AutomatedRuleApplicationManager delegate,
                                    Goal goal,
                                    FormulaTag focussedFormula,
                                    PosInOccurrence focussedSubterm,
                                    boolean onlyModifyFocussedFormula) {
        this.delegate = delegate;
        this.focussedFormula = focussedFormula;
        this.focussedSubterm = focussedSubterm;
        this.goal = goal;
        this.onlyModifyFocussedFormula = onlyModifyFocussedFormula;
    }
    
    public FocussedRuleApplicationManager (AutomatedRuleApplicationManager delegate,
                                   Goal goal,
                                   PosInOccurrence focussedSubterm) {
        this ( delegate,
               goal,
               goal.getFormulaTagManager ()
                   .getTagForPos ( focussedSubterm.topLevel () ),
               focussedSubterm,
               true );
        
        clearCache ();
    }

    public void clearCache () {
        delegate.clearCache ();
    }

    public AutomatedRuleApplicationManager copy () {
        return (AutomatedRuleApplicationManager)clone ();
    }

    public Object clone () {
        return new FocussedRuleApplicationManager ( delegate.copy (),
                                            null,
                                            focussedFormula,
                                            focussedSubterm,
                                            onlyModifyFocussedFormula );
    }
    
    public RuleApp peekNext () {   
	return delegate.peekNext();
    } 

    public RuleApp next () {
        final RuleApp app = delegate.next ();
        onlyModifyFocussedFormula = false;
        return app;
    }

    public void setGoal (Goal p_goal) {
        goal = p_goal;
        delegate.setGoal ( p_goal );
    }

    public void ruleAdded (RuleApp rule, PosInOccurrence pos) {
        // filter the rule applications, only allow applications within the
        // focussed subterm or to other formulas that have been added after creation
        // of the manager (we rely on the fact that the caching rule indexes only
        // report rules for modified/added formulas anyway)
        
        final PosInOccurrence focFormula = getPIOForFocussedSubterm ();

        if ( focFormula != null && pos != null ) {
            if ( isSameFormula ( pos, focFormula ) ) {
                if ( !isBelow ( focFormula, pos ) )
                    // rule app within the focussed formula, but not within the
                    // focussed subterm
                    return;
            } else {
                if ( onlyModifyFocussedFormula ) return;
            }
        } else if ( onlyModifyFocussedFormula ) {
            return;
        }
            
        delegate.ruleAdded ( rule, pos );
    }

    private boolean isSameFormula (PosInOccurrence pio1,
                                   PosInOccurrence pio2) {
        return pio2.isInAntec () == pio1.isInAntec ()
               && pio2.constrainedFormula ().equals ( pio1.constrainedFormula () );
    }

    private PosInOccurrence getPIOForFocussedSubterm () {
        final PosInOccurrence formula =
            goal.getFormulaTagManager ().getPosForTag ( focussedFormula );

        if ( formula == null ) return null;

        return
            focussedSubterm
            .replaceConstrainedFormula ( formula.constrainedFormula () );
    }
    
    private boolean isBelow (PosInOccurrence over, PosInOccurrence under) {
        final PIOPathIterator overIt = over.iterator ();
        final PIOPathIterator underIt = under.iterator ();

        while ( true ) {
            final int overChild = overIt.next ();
            final int underChild = underIt.next ();
            if ( overChild == -1 ) return true;
            if ( overChild != underChild ) return false;
        }
    }

    @Override
    public AutomatedRuleApplicationManager getDelegate () {
        return delegate;
    }
}