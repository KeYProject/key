// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 *
 */
public class LexPathOrdering implements TermOrdering {

    private final Set literalFunctionNames = new HashSet ();
    {
        literalFunctionNames.add("#");
        literalFunctionNames.add("0");
        literalFunctionNames.add("1");
        literalFunctionNames.add("2");
        literalFunctionNames.add("3");
        literalFunctionNames.add("4");
        literalFunctionNames.add("5");
        literalFunctionNames.add("6");
        literalFunctionNames.add("7");
        literalFunctionNames.add("8");
        literalFunctionNames.add("9");
        literalFunctionNames.add("Z");
        literalFunctionNames.add("neglit");
    }
    
    public int compare (Term p_a, Term p_b) {
        final CompRes res = compareHelp ( p_a, p_b );
        if ( res.lt () )
            return -1;
        else if ( res.gt () )
            return 1;
        else
            return 0;
    }

    private abstract static class CompRes {
        public boolean uncomparable () { return false; }
        public boolean eq ()           { return false; }
        public boolean gt ()           { return false; }
        public boolean lt ()           { return false; }
        public boolean geq()           { return gt() || eq(); }
        public boolean leq ()          { return lt() || eq(); }
    }

    private final static CompRes UNCOMPARABLE = new CompRes () {
        public boolean uncomparable() { return true; }
    };
    private final static CompRes EQUALS = new CompRes () {
        public boolean eq() { return true; }
    };
    private final static CompRes GREATER = new CompRes () {
        public boolean gt() { return true; }
    };
    private final static CompRes LESS = new CompRes () {
        public boolean lt() { return true; }
    };
    
    
    private final static class CacheKey {
        public final Term left;
        public final Term right;
        
        public CacheKey (final Term left, final Term right) {
            this.left = left;
            this.right = right;
        }
                
        public boolean equals (Object arg0) {
            if ( !( arg0 instanceof CacheKey ) ) return false;
            final CacheKey key0 = (CacheKey)arg0;
            return left.equals ( key0.left ) && right.equals ( key0.right );
        }
        
        public int hashCode () {
            return left.hashCode () + 2 * right.hashCode ();
        }
    }
    
    
    private final HashMap cache = new HashMap ();
    
    
    private CompRes compareHelp (Term p_a, Term p_b) {
        final CacheKey key = new CacheKey ( p_a, p_b );
        CompRes res = (CompRes)cache.get ( key );
        if ( res == null ) {
            res = compareHelp2 ( p_a, p_b );
            if ( cache.size () > 100000 ) cache.clear ();
            cache.put ( key, res );
        }
        return res;
    }

    private CompRes compareHelp2 (Term p_a, Term p_b) {
        
        if ( oneSubGeq ( p_a, p_b ) ) return GREATER;
        if ( oneSubGeq ( p_b, p_a ) ) return LESS;
        
        final int opComp = compare ( p_a.op (), p_b.op () );
        if ( opComp == 0 ) {
            final CompRes lexComp = compareSubsLex ( p_a, p_b );
            if ( lexComp.eq () ) {
                return EQUALS;
            } else if ( lexComp.gt () ) {
                if ( greaterThanSubs ( p_a, p_b, 1 ) ) return GREATER;
            } else if ( lexComp.lt () ) {
                if ( greaterThanSubs ( p_b, p_a, 1 ) ) return LESS;
            }
        }
        
        if ( opComp > 0 ) {
            if ( greaterThanSubs ( p_a, p_b, 0 ) ) return GREATER;
        } else {
            if ( greaterThanSubs ( p_b, p_a, 0 ) ) return LESS;
        }

        return UNCOMPARABLE;
    }

    private CompRes compareSubsLex(Term p_a, Term p_b) {
        int i = 0;

        while ( true ) {
            if ( i >= p_a.arity () ) {
                if ( i >= p_b.arity () )
                    return EQUALS;
                else
                    return LESS;
            }

            if ( i >= p_b.arity () ) return GREATER;

            final CompRes subRes = compareHelp ( p_a.sub ( i ), p_b.sub ( i ) );
            if ( !subRes.eq () ) return subRes;

            ++i;
        }
    }
    
    private boolean greaterThanSubs (Term p_a, Term p_b, int firstSub) {
        for ( int i = firstSub; i < p_b.arity (); ++i ) {
            if ( !compareHelp ( p_a, p_b.sub ( i ) ).gt () ) return false;
        }
        return true;
    }

    private boolean oneSubGeq (Term p_a, Term p_b) {
        for ( int i = 0; i != p_a.arity (); ++i ) {
            if ( compareHelp ( p_a.sub ( i ), p_b ).geq () ) return true;
        }
        return false;
    }
    
    /**
     * Compare the two given symbols
     * 
     * @return a number negative, zero or a number positive if <code>p_a</code>
     *         is less than, equal, or greater than <code>p_b</code>
     */
    private int compare (Operator p_a, Operator p_b) {
        if ( p_a == p_b ) return 0;

        int v = 0;
        // Search for special symbols
        {
            Integer w = getWeight ( p_a );
            if ( w == null ) {
                if ( getWeight ( p_b ) != null ) return 1;
            } else {
                v = w.intValue ();
                w = getWeight ( p_b );
                if ( w == null )
                    return -1;
                else
                    v -= w.intValue ();
            }
        }
        if ( v != 0 ) return v;

        if ( isVar ( p_a ) ) {
            if ( !isVar ( p_b ) ) return 1;
        } else {
            if ( isVar ( p_b ) ) return -1;
        }
            
	    // smaller arity is smaller
	    v = p_a.arity () - p_b.arity ();
	    if ( v != 0 ) return v;

	    // use the names of the symbols
	    v = p_a.name ().compareTo ( p_b.name () );
	    if ( v != 0 ) return v;

	    // HACK: compare the hash values of the two symbols
	    return sign ( p_b.hashCode () - p_a.hashCode () );
    }

    /**
     * Explicit ordering of some symbols (symbols assigned a weight by this
     * method are regarded as smaller than other symbols); symbols are ordered
     * according to their weight
     */
    private Integer getWeight (final Operator p_op) {
        final String opStr = p_op.name ().toString ();
        
        if ( literalFunctionNames.contains ( opStr ) )
                return new Integer ( 0 );
        
        if ( opStr.equals ( "neg" ) ) return new Integer ( 1 );
        if ( p_op.name().equals(AbstractIntegerLDT.CHAR_ID_NAME) ) return new Integer ( 1 );
        if ( p_op instanceof Function
             && ( (Function)p_op ).sort () == Sort.NULL )
                return new Integer ( 2 );
        if ( p_op instanceof Function
             && ( opStr.equals ( "TRUE" ) | opStr.equals ( "FALSE" ) ) )
                return new Integer ( 3 );
        if ( p_op instanceof SortDependingSymbol ) return new Integer ( 10 );
        if ( p_op instanceof AttributeOp ) return new Integer ( 20 );

        if ( opStr.equals ( "add" ) ) return new Integer ( 6 );
        if ( opStr.equals ( "mul" ) ) return new Integer ( 7 );
        if ( opStr.equals ( "div" ) ) return new Integer ( 8 );
        if ( opStr.equals ( "jdiv" ) ) return new Integer ( 9 );

        if ( p_op instanceof ProgramVariable ) {
            final ProgramVariable var = (ProgramVariable)p_op;
            if ( var.isStatic () ) return new Integer ( 30 );
            if ( var.isMember () ) return new Integer ( 31 );
            return new Integer ( 32 );
        }
        
        return null;
    }

    /**
     * @return true iff <code>op</code> is a logic variable
     */
    private boolean isVar (Operator op) {
        return op instanceof Metavariable
               || op instanceof QuantifiableVariable;
    }

    private int sign (int p) {
        if ( p > 0 ) return 1;
        else if ( p < 0 ) return -1;
        return 0;
    }

    /**
     * TODO: this should also be used when comparing terms
     * 
     * The reduction ordering on integers that is described in "A
     * critical-pair/completion algorithm for finitely generated ideals in
     * rings", with the difference that positive numbers are here considered as
     * smaller than negative numbers (with the same absolute value)
     * 
     * @return a negative number, zero, or a positive number, if <code>a</code>
     *         is smaller, equal to or greater than <code>b</code>
     */
    public static int compare(BigInteger a, BigInteger b) {
        final int c = a.abs ().compareTo ( b.abs () );
        if ( c != 0 ) return c;
        return b.signum () - a.signum ();
    }
    
    /**
     * @return the result of dividing <code>a</code> by <code>c</code>,
     *         such that the remainder becomes minimal in the reduction ordering
     *         <code>LexPathOrdering.compare</code> on integers
     */
    public static BigInteger divide(BigInteger a, BigInteger c) {
        final BigInteger[] divRem = a.divideAndRemainder ( c );
        while ( true ) {
            // could be done more efficiently. but apparently the rounding
            // behaviour of BigInteger.divide for negative numbers is not
            // properly specified. or everything becomes very tedious ...
            
            final BigInteger newRem1 = divRem[1].subtract ( c );
            if ( compare ( newRem1, divRem[1] ) < 0 ) {
                divRem[0] = divRem[0].add ( BigInteger.ONE );
                divRem[1] = newRem1;
                continue;
            }
            final BigInteger newRem2 = divRem[1].add ( c );
            if ( compare ( newRem2, divRem[1] ) < 0 ) {
                divRem[0] = divRem[0].subtract ( BigInteger.ONE );
                divRem[1] = newRem2;
                continue;
            }
            
            return divRem[0];
        }
    }
}
