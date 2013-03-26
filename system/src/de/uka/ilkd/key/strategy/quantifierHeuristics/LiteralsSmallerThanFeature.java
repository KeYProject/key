// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.SmallerThanFeature;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

public class LiteralsSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm left, right;
    private final IntegerLDT       numbers;

    private final QuanEliminationAnalyser quanAnalyser =
        new QuanEliminationAnalyser ();
    
    // ugly, but we need some services
    private Services               services = null;
    private PosInOccurrence        focus = null;

    private LiteralsSmallerThanFeature(ProjectionToTerm left,
                                       ProjectionToTerm right,
                                       IntegerLDT numbers) {
        this.left = left;
        this.right = right;
        this.numbers = numbers;
    }

    public static Feature create(ProjectionToTerm left,
                                 ProjectionToTerm right,
                                 IntegerLDT numbers) {
        return new LiteralsSmallerThanFeature ( left, right, numbers );
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        final Term leftTerm = left.toTerm ( app, pos, goal );
        final Term rightTerm = right.toTerm ( app, pos, goal );

        return compareTerms ( leftTerm, rightTerm, pos, goal.proof ().getServices () );
    }

    protected boolean compareTerms(Term leftTerm, Term rightTerm,
                                   PosInOccurrence pos, Services p_services) {
        services = p_services;
        focus = pos;
        
        final LiteralCollector m1 = new LiteralCollector ();
        m1.collect ( leftTerm );
        final LiteralCollector m2 = new LiteralCollector ();
        m2.collect ( rightTerm );

        final boolean res = lessThan ( m1.getResult(), m2.getResult() );
        
        services = null;
        focus = null;
        
        return res;
    }
    
    /**
     * this overwrites the method of <code>SmallerThanFeature</code>
     */
    protected boolean lessThan(Term t1, Term t2) {

        final int t1Def = quanAnalyser.eliminableDefinition ( t1, focus );
        final int t2Def = quanAnalyser.eliminableDefinition ( t2, focus );

        if ( t1Def > t2Def ) return true;
        if ( t1Def < t2Def ) return false;
                
        // HACK: we move literals that do not contain any variables to the left,
        // so that they can be moved out of the scope of the quantifiers
        if ( t1.freeVars ().size () == 0 ) {
            if ( t2.freeVars ().size () > 0 ) return false;
        } else {
            if ( t2.freeVars ().size () == 0 ) return true;
        }
        
        t1 = discardNegation ( t1 );
        t2 = discardNegation ( t2 );
        
        if ( isBinaryIntRelation ( t2 ) ) {
            if ( !isBinaryIntRelation ( t1 ) ) return true;
            
            int c = compare ( t1.sub ( 0 ), t2.sub ( 0 ) );
            if ( c < 0 ) return true;
            if ( c > 0 ) return false;
            
            c = comparePolynomials ( t1.sub ( 1 ), t2.sub ( 1 ) );
            if ( c < 0 ) return true;
            if ( c > 0 ) return false;
            
            final Polynomial t1RHS =
                Polynomial.create ( t1.sub ( 1 ), services );
            final Polynomial t2RHS =
                Polynomial.create ( t2.sub ( 1 ), services );
            if ( t1RHS.valueLess ( t2RHS ) ) return true;
            if ( t2RHS.valueLess ( t1RHS ) ) return false;

            c = formulaKind ( t1 ) - formulaKind ( t2 );
            if ( c < 0 ) return true;
            if ( c > 0 ) return false;
        } else {
            if ( isBinaryIntRelation ( t1 ) ) return false;
        }
        
        return super.lessThan ( t1, t2 );
    }

    private int comparePolynomials(Term t1, Term t2) {
        final Iterator<Term> it1 = new MonomialIterator ( t1 );
        final Iterator<Term> it2 = new MonomialIterator ( t2 );

        while ( true ) {
            if ( it1.hasNext () ) {
                if ( !it2.hasNext () ) return 1;
            } else {
                if ( it2.hasNext () )
                    return -1;
                else
                    return 0;
            }
            
            final int c = compare ( it1.next (), it2.next () );
            if ( c != 0 ) return c;
        }
    }
    
    private Term discardNegation(Term t) {
        while ( t.op () == Junctor.NOT )
            t = t.sub ( 0 );
        return t;
    }
    
    private boolean isBinaryIntRelation(Term t) {
        return formulaKind ( t ) >= 0;
    }

    private int formulaKind(Term t) {
        final Operator op = t.op ();
        if ( op == numbers.getLessOrEquals () ) return 1;
        if ( op == numbers.getGreaterOrEquals () ) return 2;
        if ( op == Equality.EQUALS ) return 3;
        return -1;
    }

    private class MonomialIterator implements Iterator<Term> {
        private Term polynomial;
        private Term nextMonomial = null;

        private MonomialIterator(Term polynomial) {
            this.polynomial = polynomial;
            findNextMonomial ();
        }

        private void findNextMonomial() {
            while ( nextMonomial == null && polynomial != null ) {
                if ( polynomial.op () == numbers.getAdd() ) {
                    nextMonomial = polynomial.sub ( 1 );
                    polynomial = polynomial.sub ( 0 );
                } else {
                    nextMonomial = polynomial;
                    polynomial = null;
                }

                if ( nextMonomial.op () == numbers.getNumberSymbol () )
                    nextMonomial = null;
            }
        }
        
        public boolean hasNext() {
            return nextMonomial != null;
        }

        public Term next() {
            final Term res = nextMonomial;
            nextMonomial = null;
            findNextMonomial ();
            return res;
        }
        
        /** 
         * throw an unsupported operation exception
         */
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }
    
    private class LiteralCollector extends Collector {
        protected void collect(Term te) {
            final Operator op = te.op ();
            if ( op == Junctor.OR ) {
                collect ( te.sub ( 0 ) );
                collect ( te.sub ( 1 ) );
            } else {
                addTerm ( te );
            }
        }
    }

}
