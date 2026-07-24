/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.math.BigInteger;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.sort.NullSort;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.StripedLruCache;
import org.key_project.util.collection.ImmutableArray;

/**
 *
 */
public class LexPathOrdering implements TermOrdering {

    /**
     * Per-comparison memo, scoped to one top-level {@link #compare(Term, Term)} call. The
     * recursion of {@link #compareHelp} visits the pair-DAG of the two terms; on large terms with
     * structural sharing that DAG has far more distinct pairs than the bounded global
     * {@link #cache} can hold, so the LRU is evicted mid-comparison and memoization collapses,
     * measured 2000M compareHelp calls (960M recomputations, 134s) for 1.68M comparisons on
     * an ips4o goal at 6000 proof steps. An unbounded per-call map restores true DAG complexity
     * (same run: 92M calls, 7.8s, byte-identical results). ThreadLocal because a LexPathOrdering
     * instance is shared across parallel-prover workers; the map is reused (cleared) per call, so
     * small comparisons pay only an empty-map lookup.
     */
    private final ThreadLocal<java.util.HashMap<CacheKey, CompRes>> callMemo =
        ThreadLocal.withInitial(java.util.HashMap::new);

    public int compare(Term p_a, Term p_b) {
        final java.util.HashMap<CacheKey, CompRes> memo = callMemo.get();
        memo.clear(); // scope the memo to this top-level comparison
        final CompRes res;
        try {
            res = compareHelp(p_a, p_b);
        } finally {
            memo.clear();
        }
        if (res.lt()) {
            return -1;
        } else if (res.gt()) {
            return 1;
        } else {
            return 0;
        }
    }

    private abstract static class CompRes {

        // used in anonymous classes inheriting from CompRes
        @SuppressWarnings("unused")
        public boolean uncomparable() { return false; }

        public boolean eq() { return false; }

        public boolean gt() { return false; }

        public boolean lt() { return false; }

        public boolean geq() { return gt() || eq(); }

        // kept for symmetry reasons
        @SuppressWarnings("unused")
        public boolean leq() { return lt() || eq(); }
    }

    private final static CompRes UNCOMPARABLE = new CompRes() {
        public boolean uncomparable() { return true; }
    };
    private final static CompRes EQUALS = new CompRes() {
        public boolean eq() { return true; }
    };
    private final static CompRes GREATER = new CompRes() {
        public boolean gt() { return true; }
    };
    private final static CompRes LESS = new CompRes() {
        public boolean lt() { return true; }
    };


    private record CacheKey(Term left, Term right) {
    }


    /**
     * Comparison-result cache, a thread-safe bounded LRU. A {@link LexPathOrdering} lives in a
     * per-proof strategy cost feature ({@code SmallerThanFeature}) shared across all goals, and the
     * parallel prover evaluates rule-application cost concurrently, so this cache is read and
     * written by several workers at once. The cached {@link CompRes} is a pure
     * function of the key (the ordering of two fixed terms is fully determined by them), so
     * eviction order never changes a result, only the hit rate. We therefore use the
     * lower-contention {@link StripedLruCache} (per-segment locking) rather than the single-lock
     * {@code ConcurrentLruCache}.
     */
    private final StripedLruCache<CacheKey, CompRes> cache =
        new StripedLruCache<>(10000, 16);


    private CompRes compareHelp(Term p_a, Term p_b) {
        final CacheKey key = new CacheKey(p_a, p_b);
        final java.util.HashMap<CacheKey, CompRes> memo = callMemo.get();
        final CompRes local = memo.get(key);
        if (local != null) {
            return local;
        }
        CompRes res = cache.get(key);
        if (res == null) {
            res = compareHelp2(p_a, p_b);
            cache.put(key, res);
        }
        memo.put(key, res);
        return res;
    }

    private CompRes compareHelp2(Term p_a, Term p_b) {

        if (oneSubGeq(p_a, p_b)) {
            return GREATER;
        }
        if (oneSubGeq(p_b, p_a)) {
            return LESS;
        }

        var p__a = (JTerm) p_a;
        var p__b = (JTerm) p_b;

        final int opComp =
            compare(p_a.op(), p_a.sort(), p__a.getLabels(), p_b.op(), p_b.sort(), p__b.getLabels());
        if (opComp == 0) {
            final CompRes lexComp = compareSubsLex(p_a, p_b);
            if (lexComp.eq()) {
                return EQUALS;
            } else if (lexComp.gt()) {
                if (greaterThanSubs(p_a, p_b, 1)) {
                    return GREATER;
                }
            } else if (lexComp.lt()) {
                if (greaterThanSubs(p_b, p_a, 1)) {
                    return LESS;
                }
            }
        }

        if (opComp > 0) {
            if (greaterThanSubs(p_a, p_b, 0)) {
                return GREATER;
            }
        } else {
            if (greaterThanSubs(p_b, p_a, 0)) {
                return LESS;
            }
        }

        return UNCOMPARABLE;
    }

    private CompRes compareSubsLex(Term p_a, Term p_b) {
        int i = 0;

        while (true) {
            if (i >= p_a.arity()) {
                if (i >= p_b.arity()) {
                    return EQUALS;
                } else {
                    return LESS;
                }
            }

            if (i >= p_b.arity()) {
                return GREATER;
            }

            final CompRes subRes = compareHelp(p_a.sub(i), p_b.sub(i));
            if (!subRes.eq()) {
                return subRes;
            }

            ++i;
        }
    }

    private boolean greaterThanSubs(Term p_a, Term p_b, int firstSub) {
        for (int i = firstSub; i < p_b.arity(); ++i) {
            if (!compareHelp(p_a, p_b.sub(i)).gt()) {
                return false;
            }
        }
        return true;
    }

    private boolean oneSubGeq(Term p_a, Term p_b) {
        for (int i = 0; i != p_a.arity(); ++i) {
            if (compareHelp(p_a.sub(i), p_b).geq()) {
                return true;
            }
        }
        return false;
    }

    /**
     * Compare the two given symbols
     *
     * @return a number negative, zero or a number positive if <code>p_a</code> is less than, equal,
     *         or greater than <code>p_b</code>
     */
    private int compare(Operator aOp, Sort aSort,
            ImmutableArray<TermLabel> aLabels, Operator bOp,
            Sort bSort, ImmutableArray<TermLabel> bLabels) {
        if (aOp == bOp) {
            return 0;
        }

        // Search for literals
        int v = literalWeighter.compareWeights(aOp, bOp);
        if (v != 0) {
            return v;
        }

        if (isVar(aOp)) {
            if (!isVar(bOp)) {
                return 1;
            }
        } else {
            if (isVar(bOp)) {
                return -1;
            }
        }

        // compare the sorts of the symbols: more specific sorts are smaller
        v = getSortDepth(bSort) - getSortDepth(aSort);
        if (v != 0) {
            return v;
        }

        // Search for special function symbols
        v = functionWeighter.compareWeights(aOp, bOp);
        if (v != 0) {
            return v;
        }

        // smaller arity is smaller
        v = aOp.arity() - bOp.arity();
        if (v != 0) {
            return v;
        }

        // compare anonHeap labels: if only one term has an anonHeap label,
        // then this is smaller
        v = (aLabels.contains(ParameterlessTermLabel.ANON_HEAP_LABEL) ? -1 : 0);
        v += (bLabels.contains(ParameterlessTermLabel.ANON_HEAP_LABEL) ? 1 : 0);
        if (v != 0) {
            return v;
        }

        // use the names of the symbols
        v = aOp.name().compareTo(bOp.name());
        return v;

        // HACK: compare the hash values of the two symbols
        // return sign ( bOp.hashCode () - aOp.hashCode () );
        // The two functions have the same name, consider them
        // equal for the sake of this comparison.
        // Otherwise the proof is indeterministic as the hash
        // codes may change from run to run. (MU)
    }


    /**
     * Hashmap from <code>Sort</code> to <code>Integer</code>, storing the lengths of maximal paths
     * from a sort to the top element of the sort lattice.
     */
    // Thread-safe: shared via the per-proof cost feature and read/written by parallel workers (see
    // the comparison cache above). A WeakHashMap even mutates on get (stale-entry expunge), so
    // plain
    // concurrent access would corrupt it; the synchronized wrapper makes each op atomic (the
    // get-then-put is a benign idempotent recompute), keeping the weak-key semantics.
    private final Map<Sort, Integer> sortDepthCache =
        Collections.synchronizedMap(new WeakHashMap<>());

    /**
     * @return the length of the longest path from <code>s</code> to the top element of the sort
     *         lattice. Probably this length is not computed correctly here, because the
     *         representation of sorts in key is completely messed up, but you get the idea
     */
    private int getSortDepth(Sort s) {
        Integer res = sortDepthCache.get(s);
        if (res == null) {
            res = getSortDepthHelp(s);
            sortDepthCache.put(s, res);
        }
        return res;
    }

    private int getSortDepthHelp(Sort s) {
        int res = -1;

        // HACKish: ensure that object sorts are bigger than primitive sorts
        final String sName = s.name().toString();
        if ("int".equals(sName)) {
            res = 10000;
        }
        if ("boolean".equals(sName)) {
            res = 20000;
        }
        if (s instanceof NullSort) {
            return 30000;
        }

        for (Sort sort : s.extendsSorts()) {
            res = Math.max(res, getSortDepth(sort));
        }

        return res + 1;
    }

    ////////////////////////////////////////////////////////////////////////////

    /**
     * Base class for metrics on symbols that are used to construct an ordering
     */
    private static abstract class Weighter {

        /**
         * Compare the weights of two symbols using the function <code>getWeight</code>.
         *
         * @return a number negative, zero or a number positive if the weight of <code>p_a</code> is
         *         less than, equal, or greater than the weight of <code>p_b</code>
         */
        public int compareWeights(Operator p_a, Operator p_b) {
            final Integer aWeight = getWeight(p_a);
            final Integer bWeight = getWeight(p_b);

            if (aWeight == null) {
                if (bWeight == null) {
                    return 0;
                } else {
                    return 1;
                }
            } else {
                if (bWeight == null) {
                    return -1;
                } else {
                    return aWeight - bWeight;
                }
            }
        }

        protected abstract Integer getWeight(Operator p_op);
    }

    /**
     * Explicit ordering of literals (symbols assigned a weight by this class are regarded as
     * smaller than all other symbols)
     */
    private static class LiteralWeighter extends Weighter {

        private final Set<String> intFunctionNames = new LinkedHashSet<>();
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

        private final Set<String> theoryFunctionNames = new LinkedHashSet<>();
        {
            theoryFunctionNames.add("C");
            theoryFunctionNames.add("seqEmpty");
            theoryFunctionNames.add("empty");

            theoryFunctionNames.add("strPool");
        }



        protected Integer getWeight(Operator p_op) {

            final String opStr = p_op.name().toString();

            if (intFunctionNames.contains(opStr) || theoryFunctionNames.contains(opStr)) {
                return 0;
            }

            if (opStr.equals("allLocs")) {
                return 1;
            } else if (opStr.equals("allObjects")) {
                return 2;
            } else if (opStr.equals("allFields")) {
                return 3;
            } else if (opStr.equals("singleton")) {
                return 4;
            } else if (opStr.equals("freshLocs")) {
                return 5;
            }

            if (opStr.equals("neg")) {
                return 1;
            }

            if (p_op.name().equals(IntegerLDT.CHAR_ID_NAME)) {
                return 1;
            }
            if (p_op instanceof Function && ((Function) p_op).sort() instanceof NullSort) {
                return 2;
            }
            if (p_op instanceof Function && (opStr.equals("TRUE") || opStr.equals("FALSE"))) {
                return 3;
            }

            if (opStr.equals("add")) {
                return 6;
            }
            if (opStr.equals("mul")) {
                return 7;
            }
            if (opStr.equals("div")) {
                return 8;
            }
            if (opStr.equals("jdiv")) {
                return 9;
            }


            if (opStr.equals("intersect")) {
                return 6;
            }
            if (opStr.equals("union")) {
                return 7;
            }
            if (opStr.equals("infiniteUnion")) {
                return 8;
            }
            if (opStr.equals("setMinus")) {
                return 9;
            }


            if (opStr.equals("seqSingleton")) {
                return 6;
            }
            if (opStr.equals("seqConcat")) {
                return 7;
            }


            if (opStr.equals("msetSingle")) {
                return 6;
            }
            if (opStr.equals("msetSum")) {
                return 7;
            }
            return null;
        }
    }

    /**
     * Explicit ordering for different kinds of function symbols; symbols like C::<get> or
     * C.<nextToCreate> should be smaller than other symbols
     */
    private static class FunctionWeighter extends Weighter {
        protected Integer getWeight(Operator p_op) {
            final String opStr = p_op.name().toString();

            if (opStr.equals("heap")) {
                return 0;
            }
            if (p_op instanceof Function && ((Function) p_op).isUnique()) {
                return 5;
            }
            if (opStr.equals("pair")) {
                return 10;
            }


            /*
             * if ( p_op instanceof SortDependingSymbol ) return new Integer ( 10 );
             *
             * if ( p_op instanceof AttributeOp ) return new Integer ( 20 );
             *
             * if ( p_op instanceof ProgramVariable ) { final ProgramVariable var =
             * (ProgramVariable)p_op; if ( var.isStatic () ) return new Integer ( 30 ); if (
             * var.isMember () ) return new Integer ( 31 ); return new Integer ( 32 ); }
             */

            return null;
        }
    }

    private final Weighter literalWeighter = new LiteralWeighter();
    private final Weighter functionWeighter = new FunctionWeighter();

    ////////////////////////////////////////////////////////////////////////////

    /**
     * @return true iff <code>op</code> is a logic variable
     */
    private boolean isVar(Operator op) {
        return op instanceof QuantifiableVariable;
    }

    /**
     * TODO: this should also be used when comparing terms
     *
     * The reduction ordering on integers that is described in "A critical-pair/completion algorithm
     * for finitely generated ideals in rings", with the difference that positive numbers are here
     * considered as smaller than negative numbers (with the same absolute value)
     *
     * @return a negative number, zero, or a positive number, if <code>a</code> is smaller, equal to
     *         or greater than <code>b</code>
     */
    public static int compare(BigInteger a, BigInteger b) {
        final int c = a.abs().compareTo(b.abs());
        if (c != 0) {
            return c;
        }
        return b.signum() - a.signum();
    }

    /**
     * @return the result of dividing <code>a</code> by <code>c</code>, such that the remainder
     *         becomes minimal in the reduction ordering <code>LexPathOrdering.compare</code> on
     *         integers
     */
    public static BigInteger divide(BigInteger a, BigInteger c) {
        final BigInteger[] divRem = a.divideAndRemainder(c);
        while (true) {
            // could be done more efficiently. but apparently the rounding
            // behaviour of BigInteger.divide for negative numbers is not
            // properly specified. or everything becomes very tedious ...

            final BigInteger newRem1 = divRem[1].subtract(c);
            if (compare(newRem1, divRem[1]) < 0) {
                divRem[0] = divRem[0].add(BigInteger.ONE);
                divRem[1] = newRem1;
                continue;
            }
            final BigInteger newRem2 = divRem[1].add(c);
            if (compare(newRem2, divRem[1]) < 0) {
                divRem[0] = divRem[0].subtract(BigInteger.ONE);
                divRem[1] = newRem2;
                continue;
            }

            return divRem[0];
        }
    }
}
