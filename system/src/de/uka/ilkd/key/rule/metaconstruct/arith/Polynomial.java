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

package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;
import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Class for analysing and modifying polynomial expressions over the integers
 */
public class Polynomial {

    private final BigInteger constantPart;
    private final ImmutableList<Monomial> parts;

    private Polynomial(ImmutableList<Monomial> parts, BigInteger constantPart) {
        this.parts = parts;
        this.constantPart = constantPart;
    }
    
    private static final BigInteger MINUS_ONE = BigInteger.valueOf ( -1 );

    public final static Polynomial ZERO =
        new Polynomial ( ImmutableSLList.<Monomial>nil(), BigInteger.ZERO );    
    public final static Polynomial ONE =
        new Polynomial ( ImmutableSLList.<Monomial>nil(), BigInteger.ONE );    

    public static Polynomial create(Term polyTerm, Services services) {
        Polynomial res = services.getCaches().getPolynomialCache().get ( polyTerm );
        if ( res == null ) {
            res = createHelp ( polyTerm, services );
            services.getCaches().getPolynomialCache().put ( polyTerm, res );
        }
        return res;
    }

    private static Polynomial createHelp(Term polynomial, Services services) {
        final Analyser a = new Analyser ( services );
        a.analyse ( polynomial );
        return new Polynomial ( a.parts, a.constantPart );
    }

    public Polynomial multiply(BigInteger c) {
        if ( c.signum () == 0 )
            return new Polynomial ( ImmutableSLList.<Monomial>nil(), BigInteger.ZERO );
        ImmutableList<Monomial> newParts = ImmutableSLList.<Monomial>nil();
        for (Monomial part : parts) newParts = newParts.prepend(part.multiply(c));

        return new Polynomial ( newParts, constantPart.multiply ( c ) );
    }

    public Polynomial multiply(Monomial m) {
        if ( m.getCoefficient ().signum () == 0 )
            return new Polynomial ( ImmutableSLList.<Monomial>nil(), BigInteger.ZERO );
        
        ImmutableList<Monomial> newParts = ImmutableSLList.<Monomial>nil();
        for (Monomial part : parts) newParts = newParts.prepend(part.multiply(m));

        if ( m.getParts ().isEmpty () )
            return new Polynomial ( newParts,
                                    constantPart.multiply ( m.getCoefficient () ) );
        
        newParts = addPart ( newParts, m.multiply ( constantPart ) );
        return new Polynomial ( newParts, BigInteger.ZERO );
    }

    public Polynomial add(BigInteger c) {
        return new Polynomial ( parts, constantPart.add ( c ) );
    }
    
    public Polynomial sub(Polynomial p) {
        final BigInteger newConst =
            getConstantTerm ().subtract ( p.getConstantTerm () );
        ImmutableList<Monomial> newParts = parts;
        for (Monomial monomial : p.getParts()) newParts = addPart(newParts, monomial.multiply(MINUS_ONE));
        return new Polynomial ( newParts, newConst );
    }
    
    public Polynomial add(Monomial m) {
        if ( m.getParts ().isEmpty () )
            return new Polynomial ( parts,
                                    constantPart.add ( m.getCoefficient () ) );

        return new Polynomial ( addPart ( parts, m ), constantPart );
    }
    
    public Polynomial add(Polynomial p) {
        final BigInteger newConst =
            getConstantTerm ().add ( p.getConstantTerm () );
        ImmutableList<Monomial> newParts = parts;
        for (Monomial monomial : p.getParts()) newParts = addPart(newParts, monomial);
        return new Polynomial ( newParts, newConst );
    }
    
    /**
     * @return the greatest common divisor of the coefficients of the monomials
     *         of this polynomial. The constant part of the polynomial is not
     *         taken into account. If there are no monomials (apart from the
     *         constant term), the result is <code>BigInteger.ZERO</code>
     */
    public BigInteger coeffGcd() {
        BigInteger res = BigInteger.ZERO;
        for (Monomial part : parts) res = res.gcd(part.getCoefficient());
        return res;
    }
    
    /**
     * @return <code>true</code> if the value of <code>this</code> will
     *         always be less than the value of <code>p</code>
     *         (i.e., same monomials, but the constant part is less or equal)
     */
    public boolean valueLess(Polynomial p) {
        if ( !sameParts ( p ) ) return false;
        return constantPart.compareTo ( p.constantPart ) < 0;
    }

    /**
     * @return <code>true</code> if the value of <code>this</code> will
     *         always be equal to the value of <code>p</code>
     *         (i.e., same monomials and same constant part)
     */
    public boolean valueEq(Polynomial p) {
        if ( !sameParts ( p ) ) return false;
        return constantPart.equals ( p.constantPart );
    }

    public boolean valueUneq(Polynomial p) {
        if ( !sameParts ( p ) ) return false;
        return !constantPart.equals ( p.constantPart );
    }

    public boolean valueEq(BigInteger c) {
        if ( !parts.isEmpty () ) return false;
        return constantPart.equals ( c );
    }

    public boolean valueUneq(BigInteger c) {
        if ( !parts.isEmpty () ) return false;
        return !constantPart.equals ( c );
    }

    /**
     * @return <code>true</code> if the value of <code>this</code> will
     *         always be less or equal than the value of <code>p</code>
     *         (i.e., same monomials, but the constant part is less or equal)
     */
    public boolean valueLeq(Polynomial p) {
        if ( !sameParts ( p ) ) return false;
        return constantPart.compareTo ( p.constantPart ) <= 0;
    }

    public boolean valueLess(BigInteger c) {
        if ( !parts.isEmpty () ) return false;
        return constantPart.compareTo ( c ) < 0;
    }

    public boolean valueGeq(BigInteger c) {
        if ( !parts.isEmpty () ) return false;
        return constantPart.compareTo ( c ) >= 0;
    }

    public boolean sameParts(Polynomial p) {
        if ( parts.size () != p.parts.size () ) return false;
        return difference ( parts, p.parts ).isEmpty ();
    }
    
    public Term toTerm (Services services) {
        final Operator add = 
            services.getTypeConverter().getIntegerLDT().getAdd();
        Term res = null;
        
        final Iterator<Monomial> it = parts.iterator ();
        if ( it.hasNext () ) {
            res = it.next ().toTerm ( services );
            while ( it.hasNext () )
                res = services.getTermFactory().createTerm
                              ( add, res, it.next ().toTerm ( services ) );
        }
        
        final Term cTerm = services.getTermBuilder().zTerm(constantPart.toString());
        
        if ( res == null )
            res = cTerm;
        else if ( !BigInteger.ZERO.equals ( constantPart ) )
            res = services.getTermFactory().createTerm ( add, cTerm, res );
        
        return res;        
    }
    
    public String toString() {
        final StringBuffer res = new StringBuffer ();
        res.append ( constantPart );

        for (Monomial part : parts) res.append(" + ").append(part);

        return res.toString ();        
    }
    
    private static class Analyser {
        public BigInteger constantPart = BigInteger.ZERO;
        public ImmutableList<Monomial> parts = ImmutableSLList.<Monomial>nil();
        private final Services services;
        private final TypeConverter tc;
        private final Operator numbers, add;
            
        public Analyser(final Services services) {
            this.services = services;
            this.tc = services.getTypeConverter ();
            final IntegerLDT intLDT = tc.getIntegerLDT ();
            numbers = intLDT.getNumberSymbol ();
            add = intLDT.getAdd();
        }
        
        public void analyse(Term polynomial) {
            final Operator op = polynomial.op ();
            if ( op == add ) {
                analyse ( polynomial.sub ( 0 ) );
                analyse ( polynomial.sub ( 1 ) );
            } else if ( op == numbers ) {
                final BigInteger c =
                    new BigInteger ( AbstractTermTransformer
                                     .convertToDecimalString ( polynomial, services ) );
                constantPart = constantPart.add ( c );
            } else if ( op instanceof SortDependingFunction
        	        && ((SortDependingFunction)op).getKind().equals(Sort.CAST_NAME)
                        && polynomial.sub ( 0 ).sort ().extendsTrans (
                                             tc.getIntegerLDT ().targetSort () )
                        &&
                        ( /*polynomial.sort () == tc.getByteLDT ().targetSort ()
                          || polynomial.sort () == tc.getShortLDT ().targetSort ()
                          || polynomial.sort () == tc.getCharLDT ().targetSort ()
                          || polynomial.sort () == tc.getIntLDT ().targetSort ()
                          || polynomial.sort () == tc.getLongLDT ().targetSort ()
                          || */polynomial.sort () == tc.getIntegerLDT ().targetSort () ) ) {
                // HACK: work around the hackish integer type hierarchy
                analyse ( polynomial.sub ( 0 ) );
            } else {
                parts = addPart ( parts,
                                  Monomial.create ( polynomial, services ) );
            }
        }
    }

    /**
     * @return the list of all monomials that occur in <code>a</code> but not
     *         in <code>b</code>. multiplicity is treated as well here, so
     *         this is really difference of multisets
     */
    private static ImmutableList<Monomial> difference(ImmutableList<Monomial> a, ImmutableList<Monomial> b) {
        ImmutableList<Monomial> res = a;
        final Iterator<Monomial> it = b.iterator ();
        while ( it.hasNext () && !res.isEmpty () )
            res = res.removeFirst ( it.next () );
        return res;
    }

    private static ImmutableList<Monomial> addPart(ImmutableList<Monomial> oldParts, Monomial m) {
        if ( m.getCoefficient ().signum () == 0 ) return oldParts;
        final ImmutableList<Monomial> newParts = addPartHelp ( oldParts, m );
        if ( newParts != null ) return newParts;
        return oldParts.prepend ( m );
    }

    private static ImmutableList<Monomial> addPartHelp(ImmutableList<Monomial> oldParts, Monomial m) {
        if ( oldParts.isEmpty () ) return null;
        final Monomial head = oldParts.head ();
        final ImmutableList<Monomial> tail = oldParts.tail ();
        if ( head.variablesEqual ( m ) ) {
            final Monomial newHead =
                head.addToCoefficient ( m.getCoefficient () );
            if ( newHead.getCoefficient ().signum () == 0 ) return tail;
            return tail.prepend ( newHead );
        }
        final ImmutableList<Monomial> res = addPartHelp ( tail, m );
        if ( res == null ) return null;
        return res.prepend ( head );
    }    
    
    public BigInteger getConstantTerm() {
        return constantPart;
    }

    public ImmutableList<Monomial> getParts() {
        return parts;
    }
}