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
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;


/**
 * Term generator for infering the range of values that a variable can have from
 * a given non-linear (in)equation. The generator may only be called on formulas
 * of the form
 * <tt>v^n = l</code>, <tt>v^n <= l</code>, <tt>v^n >= l</code>,
 * where <tt>v</tt> is an atomic term (does not start with
 * addition or multiplication) and <tt>l</tt> is a literal. The generator will
 * then produce at most one formula that describes the solutions of the formula
 * using linear (in)equations.
 */
public class RootsGenerator implements TermGenerator {

    private final ProjectionToTerm powerRelation;

    final TermBuilder tb = TermBuilder.DF;        
    private final BigInteger one = BigInteger.ONE;
    private final BigInteger two = BigInteger.valueOf ( 2 );

    public static TermGenerator create(ProjectionToTerm powerRelation) {
        return new RootsGenerator ( powerRelation );
    }
    
    private RootsGenerator(ProjectionToTerm powerRelation) {
        this.powerRelation = powerRelation;
    }

    public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Services services = goal.proof ().getServices ();
        final IntegerLDT numbers = services.getTypeConverter ().getIntegerLDT ();
        
        final Term powerRel = powerRelation.toTerm ( app, pos, goal );
        
        final Operator op = powerRel.op ();
        
        assert op.arity () == 2;
        
        final BigInteger lit =
            new BigInteger ( AbstractTermTransformer
                             .convertToDecimalString ( powerRel.sub ( 1 ),
                                                       services ) );
        
        final Monomial mon = Monomial.create ( powerRel.sub ( 0 ), services );
        final int pow = mon.getParts ().size ();
        if ( pow <= 1 || !mon.getCoefficient ().equals ( one ) )
            return emptyIterator ();

        final Term var = mon.getParts ().head ();
        if ( !mon.getParts ().removeAll ( var ).isEmpty () )
            return emptyIterator ();
        
        if ( op == numbers.getLessOrEquals () ) {
            return toIterator ( breakDownLeq ( var, lit, pow, services ) );
        } else if ( op == numbers.getGreaterOrEquals() ) {
            return toIterator ( breakDownGeq ( var, lit, pow, services ) );
        } else if (op == Equality.EQUALS) {
            return toIterator ( breakDownEq ( var, lit, pow, services ) );
        }
        
        return emptyIterator ();        
    }

    private Iterator<Term> emptyIterator() {
        return ImmutableSLList.<Term>nil().iterator ();
    }

    private Iterator<Term> toIterator(Term res) {
        if ( res.equals ( tb.ff () ) ) return emptyIterator ();
        return ImmutableSLList.<Term>nil().prepend ( res ).iterator ();
    }

    private Term breakDownEq(Term var, BigInteger lit, int pow,
                             Services services) {
        final Term zero = tb.zero(services);

        if ( ( pow % 2 == 0 ) ) {
            // the even case
         
            switch ( lit.signum () ) {
            case -1:
                // no solutions
                return tb.ff ();
            case 0:
                // exactly one solution
                return tb.equals ( var, zero );
            case 1:
                final BigInteger r = root ( lit, pow );
                if ( power ( r, pow ).equals ( lit ) ) {
                    // two solutions
                    final Term rTerm = tb.zTerm ( services, r.toString () );
                    final Term rNegTerm = tb.zTerm ( services, r.negate ().toString () );
                    return tb.or ( tb.or ( tb.lt ( var, rNegTerm, services ),
                                           tb.gt ( var, rTerm, services ) ),
                                   tb.and ( tb.gt ( var, rNegTerm, services ),
                                            tb.lt ( var, rTerm, services ) ) );
                } else {
                    // no solution
                    return tb.ff ();
                }
            }
        } else {
            // the odd case
            
            final BigInteger r = root ( lit, pow );
            if ( power ( r, pow ).equals ( lit ) ) {
                // one solution
                final Term rTerm = tb.zTerm ( services, r.toString () );
                return tb.equals ( var, rTerm );
            } else {
                // no solution
                return tb.ff ();
            }
        }

        assert false; // unreachable
        return null;
    }

    private Term breakDownGeq(Term var, BigInteger lit, int pow, Services services) {
        if ( ( pow % 2 == 0 ) ) {
            // the even case
            
            switch ( lit.signum () ) {
            case -1:
            case 0:
                // the inequation is no restriction
                return tb.ff ();
            case 1:
                final BigInteger r = rootRoundingUpwards ( lit, pow );
                final Term rTerm = tb.zTerm ( services, r.toString () );
                final Term rNegTerm = tb.zTerm ( services, r.negate ().toString () );
                return tb.or ( tb.leq ( var, rNegTerm, services ),
                               tb.geq ( var, rTerm, services ) );
            }
        } else {
            // the odd case

            return tb.geq ( var,
                            tb.zTerm ( services,
                                       rootRoundingUpwards ( lit, pow ).toString () ),
                            services );
        }
        
        assert false; // unreachable
        return null;
    }

    private Term breakDownLeq(Term var, BigInteger lit, int pow, Services services) {
        if ( ( pow % 2 == 0 ) ) {
            // the even case
            
            switch ( lit.signum () ) {
            case -1:
                // no solutions
                return tb.ff ();
            case 0:
                return tb.equals ( var, tb.zero( services ) );
            case 1:
                final BigInteger r = root ( lit, pow );
                final Term rTerm = tb.zTerm ( services, r.toString () );
                final Term rNegTerm = tb.zTerm ( services, r.negate ().toString () );
                return tb.and ( tb.geq ( var, rNegTerm, services ),
                                tb.leq ( var, rTerm, services ) );
            }
        } else {
            // the odd case

            return tb.leq ( var,
                            tb.zTerm ( services, root ( lit, pow ).toString () ),
                            services );
        }

        assert false; // unreachable
        return null;
    }

    /**
     * @return a number <tt>res</tt> with the property
     *         <tt>prod in ((res-1)^exp, res^exp]</tt>
     */
    private BigInteger rootRoundingUpwards(BigInteger prod, int exp) {
        final BigInteger res = root ( prod, exp );
        if ( power ( res, exp ).compareTo ( prod ) < 0 )
            return res.add ( one );
        return res;
    }

    /**
     * @return a number <tt>res</tt> with the property
     *         <tt>prod in [res^exp, (res+1)^exp)</tt>
     */
    private BigInteger root (BigInteger prod, int exp) {
        assert exp > 0;

        if ( prod.signum () >= 0 ) {
            return posRoot ( prod, exp );
        } else {
            assert exp % 2 != 0;

            BigInteger res = posRoot ( prod.abs (), exp ).negate ();
            while ( power ( res, exp ).compareTo ( prod ) > 0 )
                res = res.subtract ( one );

            return res;
        }
    }

    private BigInteger posRoot(BigInteger prod, int exp) {
        assert exp > 0;
        assert prod.signum () >= 0;

        // binary search for finding the root
        
        BigInteger lb = BigInteger.ZERO;
        BigInteger ub = prod;
        while ( !power ( lb, exp ).equals ( prod )
                && ub.subtract ( lb ).compareTo ( one ) > 0 ) {
            final BigInteger mid = ub.add ( lb ).divide ( two );
            if ( power ( mid, exp ).compareTo ( prod ) <= 0 ) {
                lb = mid;
            } else {
                ub = mid;
            }
        }
        return lb;
    }
    
    private BigInteger power (BigInteger base, int exp) {
        assert exp >= 0;
        
        // shift-multiplier
        
        BigInteger res = BigInteger.ONE;
        while (true) {
            if ( exp % 2 != 0 ) res = res.multiply ( base );

            exp >>= 1;
            if ( exp == 0 ) return res;

            base = base.multiply ( base );
        }
    }
}
