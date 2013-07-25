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


package de.uka.ilkd.key.logic;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.WeakHashMap;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 *
 */
public class LexPathOrdering implements TermOrdering {

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
    
    
    private final HashMap<CacheKey, CompRes> cache = 
        new LinkedHashMap<CacheKey, CompRes> ();
    
    
    private CompRes compareHelp (Term p_a, Term p_b) {
        final CacheKey key = new CacheKey ( p_a, p_b );
        CompRes res = cache.get ( key );
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
        
        final int opComp = compare ( p_a.op (), p_a.sort (),
                                     p_b.op (), p_b.sort () );
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
    private int compare (Operator aOp, Sort aSort, Operator bOp, Sort bSort) {
        if ( aOp == bOp ) return 0;

        // Search for literals
        int v = literalWeighter.compareWeights ( aOp, bOp );
        if ( v != 0 ) return v;

        if ( isVar ( aOp ) ) {
            if ( !isVar ( bOp ) ) return 1;
        } else {
            if ( isVar ( bOp ) ) return -1;
        }
        
        // compare the sorts of the symbols: more specific sorts are smaller
        v = getSortDepth ( bSort ) - getSortDepth ( aSort );
        if ( v != 0 ) return v;

        // Search for special function symbols
        v = functionWeighter.compareWeights ( aOp, bOp );
        if ( v != 0 ) return v;

	    // smaller arity is smaller
	    v = aOp.arity () - bOp.arity ();
	    if ( v != 0 ) return v;

	    // use the names of the symbols
	    v = aOp.name ().compareTo ( bOp.name () );
	    if ( v != 0 ) return v;

	    // HACK: compare the hash values of the two symbols
	    //return sign ( bOp.hashCode () - aOp.hashCode () );
	    // The two functions have the same name, consider them
	    // equal for the sake of this comparison.
	    // Otherwise the proof is indeterministic as the hash
	    // codes may change from run to run. (MU)
	    return 0;
    }

    
    /**
     * Hashmap from <code>Sort</code> to <code>Integer</code>, storing the
     * lengths of maximal paths from a sort to the top element of the sort
     * lattice.
     */
    private final WeakHashMap<Sort, Integer> sortDepthCache = 
        new WeakHashMap<Sort, Integer> ();
    
    /**
     * @return the length of the longest path from <code>s</code> to the top
     *         element of the sort lattice. Probably this length is not computed
     *         correctly here, because the representation of sorts in key is 
     *         completely messed up, but you get the idea
     */
    private int getSortDepth(Sort s) {
        Integer res = sortDepthCache.get ( s );
        if ( res == null ) {
            res = Integer.valueOf ( getSortDepthHelp ( s ) );
            sortDepthCache.put ( s, res );
        }
        return res.intValue ();
    }
    
    private int getSortDepthHelp(Sort s) {
        int res = -1;

        // HACKish: ensure that object sorts are bigger than primitive sorts
        final String sName = s.name ().toString ();
        if ( "int".equals ( sName ) ) res = 10000;
        if ( "boolean".equals ( sName ) ) res = 20000;
        if ( s instanceof NullSort ) return 30000;

        for (Sort sort : s.extendsSorts()) res = Math.max(res, getSortDepth(sort));

        return res + 1;
    }
    
    ////////////////////////////////////////////////////////////////////////////
    
    /**
     * Base class for metrics on symbols that are used to construct an ordering
     */
    private static abstract class Weighter {
        
        /**
         * Compare the weights of two symbols using the function
         * <code>getWeight</code>.
         * 
         * @return a number negative, zero or a number positive if the weight of
         *         <code>p_a</code> is less than, equal, or greater than the
         *         weight of <code>p_b</code>
         */
        public int compareWeights(Operator p_a, Operator p_b) {
            final Integer aWeight = getWeight ( p_a );
            final Integer bWeight = getWeight ( p_b );
            
            if ( aWeight == null ) {
                if ( bWeight == null )
                    return 0;
                else
                    return 1;
            } else {
                if ( bWeight == null )
                    return -1;
                else
                    return aWeight.intValue () - bWeight.intValue ();
            }
        }
        
        protected abstract Integer getWeight(Operator p_op);
    }
    
    /**
     * Explicit ordering of literals (symbols assigned a weight by this
     * class are regarded as smaller than all other symbols)
     */
    private static class LiteralWeighter extends Weighter {

        private final Set<String> intFunctionNames = new LinkedHashSet<String> ();
        {
            intFunctionNames.add("#");
            intFunctionNames.add("0");
            intFunctionNames.add("1");
            intFunctionNames.add("2");
            intFunctionNames.add("3");
            intFunctionNames.add("4");
            intFunctionNames.add("5");
            intFunctionNames.add("6");
            intFunctionNames.add("7");
            intFunctionNames.add("8");
            intFunctionNames.add("9");
            intFunctionNames.add("Z");
            intFunctionNames.add("neglit");
        }

        private final Set<String> theoryFunctionNames = new LinkedHashSet<String> ();
        {
            theoryFunctionNames.add("strPool");            
            theoryFunctionNames.add("clEmpty");
            theoryFunctionNames.add("clCons");
            theoryFunctionNames.add("C");
        
            theoryFunctionNames.add("empty");
        }


        
        protected Integer getWeight(Operator p_op) {

            final String opStr = p_op.name ().toString ();

            if (intFunctionNames.contains ( opStr ) || theoryFunctionNames.contains ( opStr )) 
                return Integer.valueOf ( 0 );
               
            if (opStr.equals("allLocs")) {
                return Integer.valueOf(1);
            } else if (opStr.equals("allObjects")) {
                return Integer.valueOf(2);                    
            } else if (opStr.equals("allFields")) {
                return Integer.valueOf(3);
            } else if (opStr.equals("singleton")) {
                return Integer.valueOf(4);
            } else if (opStr.equals("freshLocs")) {
                return Integer.valueOf(5);
            }

            if ( opStr.equals ( "neg" ) ) return Integer.valueOf ( 1 );

            if ( p_op.name ().equals ( IntegerLDT.CHAR_ID_NAME ) )
                return Integer.valueOf ( 1 );
            if ( p_op instanceof Function
                 && ( (Function)p_op ).sort () instanceof NullSort )
                return Integer.valueOf ( 2 );
            if ( p_op instanceof Function
                 && ( opStr.equals ( "TRUE" ) || opStr.equals ( "FALSE" ) ) )
                return Integer.valueOf ( 3 );

            if ( opStr.equals ( "add" ) ) return Integer.valueOf ( 6 );
            if ( opStr.equals ( "mul" ) ) return Integer.valueOf ( 7 );
            if ( opStr.equals ( "div" ) ) return Integer.valueOf ( 8 );
            if ( opStr.equals ( "jdiv" ) ) return Integer.valueOf ( 9 );
            
            if ( opStr.equals ( "empty" ) ) return Integer.valueOf ( 0 );

            return null;
        }
    }

    /**
     * Explicit ordering for different kinds of function symbols; symbols like
     * C::<get> or C.<nextToCreate> should be smaller than other symbols
     */
    private static class FunctionWeighter extends Weighter {
        protected Integer getWeight(Operator p_op) {
            final String opStr = p_op.name ().toString ();

            if ( opStr.equals("heap")) return Integer.valueOf(0);
            if ( p_op instanceof Function && ((Function)p_op).isUnique()) return Integer.valueOf(5);
            if ( opStr.equals("pair")) return Integer.valueOf(10);

            
/*            if ( p_op instanceof SortDependingSymbol ) return new Integer ( 10 );

            if ( p_op instanceof AttributeOp ) return new Integer ( 20 );

            if ( p_op instanceof ProgramVariable ) {
                final ProgramVariable var = (ProgramVariable)p_op;
                if ( var.isStatic () ) return new Integer ( 30 );
                if ( var.isMember () ) return new Integer ( 31 );
                return new Integer ( 32 );
            } */ 

            return null;            
        }
    }
    
    private final Weighter literalWeighter = new LiteralWeighter ();
    private final Weighter functionWeighter = new FunctionWeighter ();
    
    ////////////////////////////////////////////////////////////////////////////
    
    /**
     * @return true iff <code>op</code> is a logic variable
     */
    private boolean isVar (Operator op) {
        return op instanceof QuantifiableVariable;
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
