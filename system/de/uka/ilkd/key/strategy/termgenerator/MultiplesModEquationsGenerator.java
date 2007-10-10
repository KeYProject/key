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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SLListOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.IteratorOfMonomial;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;
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

        if ( targetM.divides ( sourceM ) )
            return toIterator ( targetM.reduce ( sourceM ).toTerm ( services ) );

        final List cofactorPolys = extractPolys ( goal, services );

        if ( cofactorPolys.isEmpty () )
            return SLListOfTerm.EMPTY_LIST.iterator ();
        
        return computeMultiples(sourceM, targetM, cofactorPolys, services)
               .iterator();
    }

    private IteratorOfTerm toIterator(Term quotient) {
        return SLListOfTerm.EMPTY_LIST.prepend ( quotient ).iterator ();
    }

    private ListOfTerm computeMultiples(Monomial sourceM, Monomial targetM,
                                        List cofactorPolys, Services services) {
        ListOfTerm res = SLListOfTerm.EMPTY_LIST;
        
        final List cofactorMonos = new ArrayList ();
        cofactorMonos.add ( new CofactorMonomial ( targetM, Polynomial.ONE ) );

        boolean changed = true;
        while ( changed ) {
            changed = false;
            
            final Iterator polyIt = cofactorPolys.iterator ();
            while ( polyIt.hasNext () ) {
                CofactorPolynomial poly = (CofactorPolynomial)polyIt.next ();

                final Iterator monoIt = cofactorMonos.iterator ();
                while ( monoIt.hasNext () ) {
                    final CofactorMonomial mono = (CofactorMonomial)monoIt.next ();
                    final CofactorItem reduced = poly.reduce ( mono );
                    if ( reduced instanceof CofactorMonomial ) {
                        polyIt.remove ();
                        cofactorMonos.add ( reduced );
                        res = addRes ( (CofactorMonomial)reduced, sourceM,
                                       res, services );
                        changed = true;
                        break;
                    } else {
                        poly = (CofactorPolynomial)reduced;
                    }
                }
            }
        }

        return res;
    }

    private ListOfTerm addRes(CofactorMonomial newMono, Monomial sourceM,
                              ListOfTerm res, Services services) {
        final Monomial mono = newMono.mono;
        final Polynomial cofactor = newMono.cofactor;

        if ( mono.divides ( sourceM ) ) {
            final Polynomial quotient =
                cofactor.multiply ( mono.reduce ( sourceM ) );

            // if the coefficient vanishes, a polynomial division step is
            // meaningless with this parameter
            if ( !quotient.getParts ().isEmpty ()
                 || quotient.getConstantTerm ().signum () != 0 )
                return res.prepend ( quotient.toTerm ( services ) );
        }
        return res;
    }

    private List extractPolys(Goal goal, Services services) {
        final IntegerLDT numbers =
            services.getTypeConverter ().getIntegerLDT ();

        final List res = new ArrayList ();

        final IteratorOfConstrainedFormula it =
            goal.sequent ().antecedent ().iterator ();
        while ( it.hasNext () ) {
            final ConstrainedFormula cfm = it.next ();
            if ( !cfm.constraint ().isBottom () ) continue;

            final Term t = cfm.formula();
            if ( t.op () != Op.EQUALS
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
        
        public CofactorPolynomial add(CofactorMonomial mono, Monomial coeff) {
            return new CofactorPolynomial
                         ( poly.add ( mono.mono.multiply ( coeff ) ),
                           cofactor.add ( mono.cofactor.multiply ( coeff ) ) );
        }
        
        public CofactorItem reduce(CofactorMonomial mono) {
            CofactorPolynomial res = this;
            final IteratorOfMonomial it = poly.getParts ().iterator ();
            while ( it.hasNext () ) {
                final Monomial part = it.next ();
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
