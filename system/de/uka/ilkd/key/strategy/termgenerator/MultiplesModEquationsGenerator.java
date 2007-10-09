// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.termgenerator;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Try to rewrite a monomial (term) <code>source</code> so that it becomes a
 * multiple of another monomial <code>target</code>, using the equations of
 * the antecedent. This should really be done with Groebner bases, but for the
 * time being we just perform a naive search. The result is a list of
 * quotients source/target (modulo equations).
 */
public class MultiplesModEquationsGenerator implements TermGenerator {

    private final ProjectionToTerm source;
    private final ProjectionToTerm target;
    
    private MultiplesModEquationsGenerator(ProjectionToTerm source,
                                           ProjectionToTerm target) {
        this.source = source;
        this.target = target;
    }

    public static TermGenerator create(ProjectionToTerm source,
                                       ProjectionToTerm target) {
        return new MultiplesModEquationsGenerator ( source, target );
    }
    
    public IteratorOfTerm generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Services services = goal.proof ().getServices ();
        
        final Monomial sourceM =
            Monomial.create ( source.toTerm ( app, pos, goal ), services );
        final Monomial targetM =
            Monomial.create ( target.toTerm ( app, pos, goal ), services );

        if ( targetM.divides ( sourceM ) ) {
            final Term quotient = targetM.reduce ( sourceM ).toTerm ( services );
            return SLListOfTerm.EMPTY_LIST.prepend ( quotient ).iterator ();
        }

        final List monoEquations = extractEquations ( goal, services );
        if ( monoEquations.isEmpty () ) return SLListOfTerm.EMPTY_LIST.iterator ();
        
        final Iterator monoIt =
            computeMultiples ( sourceM, targetM, monoEquations, services )
            .iterator ();
        
        return new IteratorOfTerm () {
            public boolean hasNext() {
                return monoIt.hasNext ();
            }
            public Term next() {
                final Monomial mono = (Monomial)monoIt.next ();
                return targetM.reduce ( mono ).toTerm ( services );
            }
        };
    }

    private List computeMultiples(Monomial sourceM, Monomial targetM,
                                        List monoEquations, Services services) {
        final List res = new LinkedList ();
        
        final Set done = new HashSet ();
        final List todo = new LinkedList ();

        todo.add ( sourceM );
        
        int limit = Math.max ( 5, monoEquations.size () * 3 );
        
        while ( limit > 0 && !todo.isEmpty () ) {
            final Monomial mono = (Monomial)todo.remove ( 0 );

            if ( done.contains ( mono ) ) continue;
            
            --limit;
            
            final Iterator it = monoEquations.iterator ();
            while ( it.hasNext () ) {
                final MonoEquation eq = (MonoEquation)it.next ();
                final Monomial rewrittenMono = eq.applyRightToLeft ( mono );
                
                if ( rewrittenMono == null || done.contains ( rewrittenMono ) )
                    continue;
                
                if ( targetM.divides ( rewrittenMono ) )
                    addToRes ( rewrittenMono, targetM, res, services );
                else
                    todo.add ( rewrittenMono );
            }

            done.add ( mono );
        }
        
        return res;
    }

    private void addToRes(Monomial mono, Monomial targetM, List res,
                          Services services) {
        final Iterator it = res.iterator ();

        // do subsumption checks to ensure that no redundant monomials are
        // returned
        while ( it.hasNext () ) {
            final Monomial oldMono = (Monomial)it.next ();
            if ( mono.divides ( oldMono ) )
                it.remove ();
            else if ( oldMono.divides ( mono ) )
                return;
        }

        res.add ( mono );
    }

    private List extractEquations(Goal goal, Services services) {
        final List res = new ArrayList ();

        final IteratorOfConstrainedFormula it =
            goal.sequent ().antecedent ().iterator ();
        while ( it.hasNext () ) {
            final ConstrainedFormula cfm = it.next ();
            if ( !cfm.constraint ().isBottom () ) continue;
            
            final MonoEquation eq =
                MonoEquation.create ( cfm.formula (), services );
            if ( eq == null ) continue;
            
            res.add ( eq );
        }

        return res;
    }
    
    private static class MonoEquation {
        private final Monomial left;
        private final Monomial right;
        
        private MonoEquation(Monomial left, Monomial right) {
            this.left = left;
            this.right = right;
        }
        
        public static MonoEquation create(Term t, Services services) {
            final IntegerLDT numbers =
                services.getTypeConverter ().getIntegerLDT ();

            if ( t.op () != Op.EQUALS
                 || !t.sub ( 0 ).sort ().extendsTrans ( numbers.targetSort () )
                 || !t.sub ( 1 ).sort ().extendsTrans ( numbers.targetSort () )
                 || t.sub ( 1 ).op () == numbers.getArithAddition () )
                return null;
            
            final Monomial left = Monomial.create ( t.sub ( 0 ), services );
            final Monomial right = Monomial.create ( t.sub ( 1 ), services );

            return new MonoEquation ( left, right );
        }
        
        public Monomial applyRightToLeft(Monomial ori) {
            if ( !right.divides ( ori ) ) return null;
            return right.reduce ( ori ).multiply ( left );
        }
        
        public String toString() {
            return "" + left + " = " + right;
        }
    }
}
