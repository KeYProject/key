// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct.arith;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.LRUCache;

/**
 * Class for analysing and modifying monomial expressions over the integers
 */
public class Monomial {
    
    private final ListOfTerm parts;
    private final BigInteger coefficient;
    
    private Monomial(final ListOfTerm parts, final BigInteger coefficient) {
        this.parts = parts;
        this.coefficient = coefficient;
    }
    
    private static final LRUCache monomialCache = new LRUCache ( 2000 );
    
    public static final Monomial ONE = new Monomial ( SLListOfTerm.EMPTY_LIST,
                                                      BigInteger.ONE );
    
    public static Monomial create(Term monoTerm, Services services) {
        Monomial res = (Monomial)monomialCache.get ( monoTerm );
        if ( res == null ) {
            res = createHelp ( monoTerm, services );
            monomialCache.put ( monoTerm, res );
        }
        return res;
    }

    private static Monomial createHelp(Term monomial, Services services) {
        final Analyser a = new Analyser ( services );
        a.analyse ( monomial );
        return new Monomial ( a.parts, a.coeff );
    }
    
    public Monomial setCoefficient(BigInteger c) {
        return new Monomial ( parts, c );
    }
    
    public Monomial multiply(BigInteger c) {
        return new Monomial ( parts, coefficient.multiply ( c ) );
    }
    
    public Monomial multiply(Monomial m) {
        return new Monomial ( parts.prepend ( m.parts ),
                              coefficient.multiply ( m.coefficient ) );
    }
    
    public Monomial addToCoefficient(BigInteger c) {
        return new Monomial ( parts, coefficient.add ( c ) );
    }
    
    /**
     * @return true iff the monomial <code>this</code> divides the monomial
     *         <code>m</code>
     */
    public boolean divides (Monomial m) {
        if ( m.coefficient.signum () == 0 ) return true;
        if ( this.coefficient.signum () == 0 ) return false;
        if ( m.coefficient.remainder ( this.coefficient ).signum () != 0 )
                return false;
        
        return difference ( this.parts, m.parts ).isEmpty ();
    }
    
    /**
     * @return true iff the variables/parts of <code>this</code> subsume the
     *         variables of <code>m</code>, i.e., if each variable that
     *         occurs in <code>m</code> occurs in the same or a higher power
     *         in <code>this</code>
     */
    public boolean variablesSubsume(Monomial m) {
        return this.parts.size () >= m.parts.size ()
               && difference ( m.parts, this.parts ).isEmpty ();
    }
    
    public boolean variablesEqual(Monomial m) {
        return this.parts.size () == m.parts.size ()
               && this.variablesSubsume ( m );
    }
    
    public boolean variablesDisjoint(Monomial m) {
        return difference ( m.parts, this.parts ).size () == m.parts.size ();
    }
    
    /**
     * @return true iff the coefficient of <code>m</code> can be made smaller
     *         (absolutely) by subtracting a multiple of <code>this</code>
     */
    public boolean reducible(Monomial m) {
        final BigInteger a = m.coefficient;
        final BigInteger c = this.coefficient;

        if ( LexPathOrdering.compare ( a.add ( c ), a ) >= 0
             && LexPathOrdering.compare ( a.subtract ( c ), a ) >= 0 )
            return false;

        return difference ( this.parts, m.parts ).isEmpty ();
    }
    
    /**
     * @return the result of dividing the monomial <code>m</code> by the
     *         monomial <code>this</code>
     */
    public Monomial reduce(Monomial m) {
        final BigInteger a = m.coefficient;
        final BigInteger c = this.coefficient;

        if ( a.signum () == 0 || c.signum () == 0 )
            return new Monomial ( SLListOfTerm.EMPTY_LIST, BigInteger.ZERO );
        
        return new Monomial ( difference ( m.parts, this.parts ),
                              LexPathOrdering.divide ( a, c ) );
    }
    
    /**
     * @return the result of dividing the least common reducible (LCR) of
     *         monomial <code>m</code> and <code>this</code> by the monomial
     *         <code>this</code>
     */
    public Monomial divideLCR(Monomial m) {
        Debug.assertFalse ( coefficient.signum () == 0 );
        Debug.assertFalse ( m.coefficient.signum () == 0 );
        
        final ListOfTerm newParts = difference ( m.parts, this.parts );

        final BigInteger gcd = coefficient.abs ().gcd ( m.coefficient.abs () );
        return new Monomial ( newParts, m.coefficient.divide ( gcd ) );
        
        /*
         The code for groebner bases over the integers. We do not use that
         anymore and instead compute groebner bases over the rationals
         (using pseudo-reduction)
         
        // in case one the coefficient of one of the monomials divides the other
        // coefficient: simply make sure that the leading terms cancel out each
        // other. this makes the whole algorithm a bit more robust concerning
        // signs
        if ( coefficient.remainder ( m.coefficient ).signum () == 0 )
            return new Monomial ( newParts, BigInteger.ONE );
        if ( m.coefficient.remainder ( coefficient ).signum () == 0 )
            return new Monomial ( newParts, m.coefficient.divide ( coefficient ) );

        BigInteger cofactor = cofactor ( coefficient, m.coefficient );
        // (any)one of the two cofactors has to be negated
        if ( coefficient.compareTo ( m.coefficient ) < 0 )
            cofactor = cofactor.negate ();
        
        return new Monomial ( newParts, cofactor );
        */
    }

    /**
     * Extended euclidian algorithm for computing cofactors. This satisfies the
     * equation <code>gcd(a,b)=a*cofactor(a,b)+b*cofactor(b,a)</code>
     */
    private BigInteger cofactor(BigInteger v0, BigInteger v1) {
        final boolean neg = v0.signum () < 0;
        v0 = v0.abs ();
        v1 = v1.abs ();
        BigInteger c0 = BigInteger.ONE;
        BigInteger c1 = BigInteger.ZERO;
        while ( v1.signum () != 0 ) {
            final BigInteger[] divRem = v0.divideAndRemainder ( v1 );
            v0 = v1;
            v1 = divRem[1];
            final BigInteger newC = c0.subtract ( c1.multiply ( divRem[0] ) );
            c0 = c1;
            c1 = newC;
        }
        if ( neg ) return c0.negate ();
        return c0;
    }
    
    
    public Term toTerm (Services services) {
        final TermSymbol mul = 
	    services.getTypeConverter().getIntegerLDT().getArithMultiplication();
        Term res = null;
        
        final IteratorOfTerm it = parts.iterator ();
        if ( it.hasNext () ) {
            res = it.next ();
            while ( it.hasNext () )
                res = TermFactory.DEFAULT.createFunctionTerm ( mul, res,
                                                               it.next () );
        }
        
        final IntLiteral lit = new IntLiteral ( coefficient.toString () );
        final Term cTerm = services.getTypeConverter ().convertToLogicElement ( lit );

        if ( res == null )
            res = cTerm;
        else if ( !BigInteger.ONE.equals ( coefficient ) )
            res = TermFactory.DEFAULT.createFunctionTerm ( mul, res, cTerm );
        
        return res;        
    }
    
    public String toString() {
        final StringBuffer res = new StringBuffer ();
        res.append ( coefficient );
        
        final IteratorOfTerm it = parts.iterator ();
        while ( it.hasNext () )
            res.append ( " * " + it.next () );

        return res.toString ();
    }
    
    private static class Analyser {
        public BigInteger coeff = BigInteger.ONE;
        public ListOfTerm parts = SLListOfTerm.EMPTY_LIST;
        private final Services services;
        private final Operator numbers, mul;
        	
        public Analyser(final Services services) {
            this.services = services;
	    final IntegerLDT intLDT = services.getTypeConverter().getIntegerLDT();
            numbers = intLDT.getNumberSymbol();
            mul     = intLDT.getArithMultiplication();
        }
        
        public void analyse(Term monomial) {
            if ( monomial.op () == mul ) {
                analyse ( monomial.sub ( 0 ) );
                analyse ( monomial.sub ( 1 ) );
            } else if ( monomial.op () == numbers ) {
                final BigInteger c =
                    new BigInteger ( AbstractMetaOperator
                                     .convertToDecimalString ( monomial, services ) );
                coeff = coeff.multiply ( c );
            } else {
                parts = parts.prepend ( monomial );
            }
        }
    }
    

    public boolean equals(Object o) {
        if ( o == this ) return true;
        
        if ( ! ( o instanceof Monomial ) ) return false;

        final Monomial m = (Monomial)o;

        if ( !coefficient.equals ( m.coefficient ) ) return false;
        if ( parts.size () != m.parts.size () ) return false;
        return difference ( parts, m.parts ).isEmpty ();
    }
    
    public int hashCode() {
        int res = coefficient.hashCode ();
        final IteratorOfTerm it = parts.iterator ();
        while ( it.hasNext () )
            res += it.next ().hashCode ();
        return res;
    }
    
    /**
     * @return the list of all terms that occur in <code>a</code> but not in
     *         <code>b</code>. multiplicity is treated as well here, so this
     *         is really difference of multisets
     */
    private static ListOfTerm difference(ListOfTerm a, ListOfTerm b) {
        ListOfTerm res = a;
        final IteratorOfTerm it = b.iterator ();
        while ( it.hasNext () && !res.isEmpty () )
            res = res.removeFirst ( it.next () );
        return res;
    }

    public BigInteger getCoefficient() {
        return coefficient;
    }

    public ListOfTerm getParts() {
        return parts;
    }

    public boolean variablesAreCoprime(Monomial m) {
        return difference ( parts, m.parts ).equals ( parts );
    }
    
}
