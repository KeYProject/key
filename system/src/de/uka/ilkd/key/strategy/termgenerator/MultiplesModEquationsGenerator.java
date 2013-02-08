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


package de.uka.ilkd.key.strategy.termgenerator;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Try to rewrite a monomial (term) <code>source</code> so that it becomes a
 * multiple of another monomial <code>target</code>, using the integer
 * equations of the antecedent. The output of the term generator is a list of
 * polynomials <code>x</code> such that
 * <code>x * target = source (modulo ...)</code>. This is done using the
 * method introduced in "Automating elementary number-theoretic proofs using
 * Groebner bases", 2007, John Harrison. Compared to the paper, we only perform
 * a simplified Groebner basis computation, basically only consisting of
 * reduction steps with polynomials that have a single monomial. This is already
 * enough to handle many practical cases and to significantly improve polynomial
 * division modulo equations.
 * 
 * In the future, this class should also be used for instantiating explicit
 * quantifiers over the integers.
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
    
    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Services services = goal.proof ().getServices ();
        
        final Monomial sourceM =
            Monomial.create ( source.toTerm ( app, pos, goal ), services );
        final Monomial targetM =
            Monomial.create ( target.toTerm ( app, pos, goal ), services );

        if ( targetM.divides ( sourceM ) )
            return toIterator ( targetM.reduce ( sourceM ).toTerm ( services ) );

        final List<CofactorPolynomial> cofactorPolys = extractPolys ( goal, services );

        if ( cofactorPolys.isEmpty () )
            return ImmutableSLList.<Term>nil().iterator ();
        
        return computeMultiples(sourceM, targetM, cofactorPolys, services)
               .iterator();
    }

    private Iterator<Term> toIterator(Term quotient) {
        return ImmutableSLList.<Term>nil().prepend ( quotient ).iterator ();
    }

    /**
     * Compute multiples of <code>targetM</code> that are congruent to
     * <code>sourceM</code> modulo the polynomials in
     * <code>cofactorPolys</code>. The result is a list of terms x with the
     * property <code>x * targetM = sourceM (modulo ...)</code>.
     * 
     * This method will change the object <code>cofactorPolys</code>.
     */
    private ImmutableList<Term> computeMultiples(Monomial sourceM, Monomial targetM,
                                        List<CofactorPolynomial> cofactorPolys, Services services) {
        ImmutableList<Term> res = ImmutableSLList.<Term>nil();
        
        final List<CofactorItem> cofactorMonos = new ArrayList<CofactorItem> ();
        cofactorMonos.add ( new CofactorMonomial ( targetM, Polynomial.ONE ) );

        boolean changed = true;
        while ( changed ) {
            changed = false;
            
            final Iterator<CofactorPolynomial> polyIt = cofactorPolys.iterator ();
            while ( polyIt.hasNext () ) {
                CofactorPolynomial poly = polyIt.next ();

                for (CofactorItem cofactorMono : cofactorMonos) {
                    final CofactorMonomial mono = (CofactorMonomial) cofactorMono;
                    final CofactorItem reduced = poly.reduce(mono);
                    if (reduced instanceof CofactorMonomial) {
                        polyIt.remove();
                        cofactorMonos.add(reduced);
                        res = addRes((CofactorMonomial) reduced, sourceM,
                                res, services);
                        changed = true;
                        break;
                    } else {
                        poly = (CofactorPolynomial) reduced;
                    }
                }
            }
        }

        return res;
    }

    private ImmutableList<Term> addRes(CofactorMonomial newMono, Monomial sourceM,
                              ImmutableList<Term> res, Services services) {
        final Monomial mono = newMono.mono;
        final Polynomial cofactor = newMono.cofactor;

        if ( mono.divides ( sourceM ) ) {
            final Polynomial quotient =
                cofactor.multiply ( mono.reduce ( sourceM ) );

            // do not return zero, that's too easy
            if ( !quotient.getParts ().isEmpty ()
                 || quotient.getConstantTerm ().signum () != 0 )
                return res.prepend ( quotient.toTerm ( services ) );
        }
        return res;
    }

    /**
     * Extract all integer equations of the antecedent and convert them into
     * <code>Polynomial</code>s.
     * 
     * @returns a list of polynomials, stored in objects of
     *          <code>CofactorPolynomial</code>. The initial cofactor is set
     *          to zero.
     */
    private List<CofactorPolynomial> extractPolys(Goal goal, Services services) {
        final IntegerLDT numbers =
            services.getTypeConverter ().getIntegerLDT ();

        final List<CofactorPolynomial> res = new ArrayList<CofactorPolynomial> ();
     
        for (final SequentFormula cfm : goal.sequent ().antecedent ()) {

            final Term t = cfm.formula();
            if ( t.op () != Equality.EQUALS
                 || !t.sub ( 0 ).sort ().extendsTrans ( numbers.targetSort () )
                 || !t.sub ( 1 ).sort ().extendsTrans ( numbers.targetSort () ) )
                continue;

            final Polynomial left = Polynomial.create ( t.sub ( 0 ), services );
            final Polynomial right = Polynomial.create ( t.sub ( 1 ), services );

            res.add ( new CofactorPolynomial ( left.sub ( right ),
                                               Polynomial.ZERO ) );
        }

        return res;
    }

    // Some classes to hold pairs of monomials/polynomials and cofactors (again
    // polynomials).
    
    private static abstract class CofactorItem {
        public final Polynomial cofactor;

        public CofactorItem(Polynomial cofactor) {
            this.cofactor = cofactor;
        }        
    }
    
    private static class CofactorMonomial extends CofactorItem {
        public final Monomial mono;

        public CofactorMonomial(Monomial mono, Polynomial cofactor) {
            super ( cofactor );
            this.mono = mono;
        }
    }
    
    private static class CofactorPolynomial extends CofactorItem {
        public final Polynomial poly;

        public CofactorPolynomial(Polynomial poly, Polynomial cofactor) {
            super ( cofactor );
            this.poly = poly;
        }
        
        /**
         * Add <code>coeff</code> times <code>mono</code> to this
         * polynomial, adjusting the cofactor accordingly
         */
        public CofactorPolynomial add(CofactorMonomial mono, Monomial coeff) {
            return new CofactorPolynomial
                         ( poly.add ( mono.mono.multiply ( coeff ) ),
                           cofactor.add ( mono.cofactor.multiply ( coeff ) ) );
        }
        
        /**
         * Reduce the polynomial by adding a multiple of the monomial
         * <code>mono</code>. The result is either
         * <code>CofactorPolynomial</code> or <code>CofactorMonomial</code>,
         * depending on whether the resulting polynomial has one or multiple
         * monomials
         */
        public CofactorItem reduce(CofactorMonomial mono) {
            CofactorPolynomial res = this;
            
            for (final Monomial part : poly.getParts()) {
                if ( mono.mono.divides ( part ) ) {
                    final Monomial coeff = mono.mono.reduce ( part );
                    res = res.add ( mono,
                                    coeff.multiply ( BigInteger.valueOf ( -1 ) ) );
                }
            }
            if ( res.poly.getParts ().size () == 1
                 && res.poly.getConstantTerm ().signum () == 0 )                  
                return new CofactorMonomial ( res.poly.getParts ().head (),
                                              res.cofactor );
            if ( res.poly.getParts ().size () == 0
                 && res.poly.getConstantTerm ().signum () != 0 )
                return new CofactorMonomial ( Monomial.ONE.multiply
                                                ( res.poly.getConstantTerm () ),
                                              res.cofactor );
            return res;
        }
    }

}
