/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.Map;

import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.PrefixTermTacletAppIndexCacheImpl.CacheKey;
import de.uka.ilkd.key.rule.FindTaclet;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.Taclet;
import org.key_project.util.ConcurrentLruCache;
import org.key_project.util.collection.ImmutableList;

/**
 * Cache that is used for accelerating <code>TermTacletAppIndex</code>. Basically, this is a mapping
 * from terms to objects of <code>TermTacletAppIndex</code>, following the idea that the same
 * taclets will be applicable to an occurrence of the same term in different places.
 * <p>
 * There are different categories of locations/areas in a term that have to be separated, because
 * different taclets could be applicable. These are:
 * <ul>
 * <li>Toplevel in the antecedent</li>
 * <li>Toplevel in the succedent</li>
 * <li>Non-toplevel, but not below updates or programs and not below "bad" operators that we do not
 * know (defined by <code>TermTacletAppIndexCacheSet.isAcceptedOperator</code>). In this case we
 * also have to distinguish different prefixes of a position, i.e., different sets of variables that
 * are bound above a position, and different <em>polarities</em> of a position: rewrite taclets can
 * be restricted to positions of antecedent or succedent polarity
 * ({@link de.uka.ilkd.key.rule.RewriteTaclet#checkPrefix}), so the applicable taclets — the cached
 * index contents — differ between a positive, a negative and a polarity-less occurrence of the same
 * term. (Sharing entries across polarities used to make the reported rule apps depend on which
 * occurrence happened to be indexed first — across all goals sharing this cache — and thereby made
 * proof search depend on the goal scheduling order, i.e. nondeterministic under the parallel
 * prover.)</li>
 * <li>Below updates, but not below programs. We do not cache at all in such places.</li>
 * <li>Below programs. Again, we also have to distinguish different prefixes of a position. (No
 * polarity distinction is needed here: a modality above the position vetoes all
 * application-restricted rewrite taclets and makes the polarity indefinite.)</li>
 * <li>Below other "bad" operators. We do not cache at all in such places.</li>
 * </ul>
 * </p>
 * We identify these different areas with an automaton that walks from the root of a formula to a
 * subformula or subterm, roughly following the state design pattern. The transition function is
 * realised by the method <code>ITermTacletAppIndexCache.descend</code>.
 */
public class TermTacletAppIndexCacheSet {
    /**
     * max. instances of <code>ITermTacletAppIndexCache</code> that are kept in this set (e.g., for
     * different prefixes of quantified variables)
     */
    private final static int MAX_CACHE_ENTRIES = 100;

    /**
     * dummy cache that is not caching at all, and from which no other cache is reachable
     */
    private final static ITermTacletAppIndexCache noCache = new ITermTacletAppIndexCache() {
        @Override
        public ITermTacletAppIndexCache descend(Term t, int subtermIndex) {
            return this;
        }

        @Override
        public TermTacletAppIndex getIndexForTerm(Term t) {
            return null;
        }

        @Override
        public void putIndexForTerm(Term t, TermTacletAppIndex index) {}
    };

    /**
     * the toplevel caches for the antecedent and the succedent. These are the starting points when
     * determining the cache for an arbitrary position
     */
    private final ITermTacletAppIndexCache antecCache;
    private final ITermTacletAppIndexCache succCache;

    /**
     * caches for locations that are not below updates, programs or in the scope of binders, by
     * position polarity (indexed by {@code polarity + 1} for polarity -1, 0, 1)
     */
    private final ITermTacletAppIndexCache[] topLevelCachesEmptyPrefix =
        new ITermTacletAppIndexCache[3];

    /**
     * caches for locations that are not below updates or programs, but in the scope of binders.
     * this is a mapping from (binder prefix, position polarity) to <code>TopLevelCache</code>
     *
     * <p>
     * One cache set is shared across the sibling goals of a proof branch (TacletAppIndex.copyWith
     * hands on the same instance), so these prefix caches are read and written concurrently on the
     * parallel matching path -- hence ConcurrentLruCache. The exact (not striped) flavour is used
     * to
     * preserve the original global LRU eviction: re-creating an evicted sub-cache orphans its
     * instance-specific entries in the shared backend, and the number of distinct quantifier
     * prefixes is small (eviction rarely fires), so exact eviction avoids extra backend churn at
     * negligible lock cost.
     */
    private final ConcurrentLruCache<TopLevelCacheKey, ITermTacletAppIndexCache> topLevelCaches =
        new ConcurrentLruCache<>(MAX_CACHE_ENTRIES);

    /** key of the {@link #topLevelCaches} map: binder prefix plus position polarity */
    private record TopLevelCacheKey(ImmutableList<QuantifiableVariable> prefix, int polarity) {
    }

    /**
     * cache for locations that are below updates, but not below programs or in the scope of binders
     */
    private final ITermTacletAppIndexCache belowUpdateCacheEmptyPrefix =
        new BelowUpdateCache(ImmutableList.nil());

    /**
     * cache for locations that are below programs, but not in the scope of binders
     */
    private final ITermTacletAppIndexCache belowProgCacheEmptyPrefix;

    /**
     * caches for locations that are both below programs and in the scope of binders. this is a
     * mapping from <code>IList<QuantifiedVariable></code> to <code>BelowProgCache</code>
     */
    private final ConcurrentLruCache<ImmutableList<QuantifiableVariable>, ITermTacletAppIndexCache> belowProgCaches =
        new ConcurrentLruCache<>(MAX_CACHE_ENTRIES);

    private final Map<CacheKey, TermTacletAppIndex> cache;

    public TermTacletAppIndexCacheSet(Map<CacheKey, TermTacletAppIndex> cache) {
        assert cache != null;
        this.cache = cache;
        // the top-level formulas of antecedent and succedent start with definite polarity;
        // these two instances are distinct from the (nested) topLevelCachesEmptyPrefix ones
        // because top-level positions index different taclets (antecedent/succedent taclets)
        // than proper subterm positions (rewrite taclets)
        antecCache = new TopLevelCache(ImmutableList.nil(), -1, cache);
        succCache = new TopLevelCache(ImmutableList.nil(), +1, cache);
        for (int polarity = -1; polarity <= 1; polarity++) {
            topLevelCachesEmptyPrefix[polarity + 1] =
                new TopLevelCache(ImmutableList.nil(), polarity, cache);
        }
        belowProgCacheEmptyPrefix =
            new BelowProgCache(ImmutableList.nil(), cache);
    }

    ////////////////////////////////////////////////////////////////////////////

    /**
     * @return the cache for top-level locations in the antecedent
     */
    public ITermTacletAppIndexCache getAntecCache() {
        return antecCache;
    }

    /**
     * @return the cache for top-level locations in the succedent
     */
    public ITermTacletAppIndexCache getSuccCache() {
        return succCache;
    }

    /**
     * @return a dummy cache that is not caching at all, and from which no other cache is reachable
     */
    public ITermTacletAppIndexCache getNoCache() {
        return noCache;
    }

    /**
     * @return <code>true</code> iff <code>t</code> is a taclet that might be cached by any
     *         of the caches of this set
     */
    public boolean isRelevantTaclet(Taclet t) {
        return t instanceof FindTaclet;
    }
    ////////////////////////////////////////////////////////////////////////////

    /**
     * @return the cache for locations of the given polarity that are not below updates or programs
     *         and in the scope of binders binding <code>prefix</code> (which might be empty)
     */
    private ITermTacletAppIndexCache getTopLevelCache(ImmutableList<QuantifiableVariable> prefix,
            int polarity) {
        if (prefix.isEmpty()) {
            return topLevelCachesEmptyPrefix[polarity + 1];
        }
        final TopLevelCacheKey key = new TopLevelCacheKey(prefix, polarity);
        // computeIfAbsent is atomic on the ConcurrentLruCache, so concurrent misses share one
        // sub-cache instance instead of racing to create duplicates that orphan backend entries.
        return topLevelCaches.computeIfAbsent(key,
            k -> new TopLevelCache(k.prefix(), k.polarity(), cache));
    }

    /**
     * The polarity of the <code>subtermIndex</code>-th direct subterm of a term with top operator
     * <code>op</code>, given the polarity of the term itself: negation and the left-hand side of an
     * implication flip the polarity, the other junctors (and the branches of a conditional) keep
     * it, and any other operator makes it indefinite. This mirrors the polarity computation of
     * {@link de.uka.ilkd.key.rule.RewriteTaclet#checkPrefix}, which decides the applicability of
     * polarity-restricted rewrite taclets — the reason polarity is part of the cache state.
     */
    private static int childPolarity(Operator op, int subtermIndex, int polarity) {
        if (polarity == 0) {
            return 0;
        }
        if (op == Junctor.NOT || (op == Junctor.IMP && subtermIndex == 0)) {
            return -polarity;
        }
        if (op == Junctor.AND || op == Junctor.OR || (op == Junctor.IMP && subtermIndex != 0)
                || (op == IfThenElse.IF_THEN_ELSE && subtermIndex != 0)) {
            return polarity;
        }
        return 0;
    }

    /**
     * @return the cache for locations that are below programs and in the scope of binders binding
     *         <code>prefix</code> (which might be empty)
     */
    private ITermTacletAppIndexCache getBelowProgCache(ImmutableList<QuantifiableVariable> prefix) {
        if (prefix.isEmpty()) {
            return belowProgCacheEmptyPrefix;
        }
        // computeIfAbsent is atomic: concurrent misses share one sub-cache instance (see
        // getTopLevelCache).
        return belowProgCaches.computeIfAbsent(prefix, p -> new BelowProgCache(p, cache));
    }

    /**
     * @return the cache for locations that are below updates, but not below programs, and that are
     *         in the scope of binders binding <code>prefix</code> (which might be empty)
     */
    private ITermTacletAppIndexCache getBelowUpdateCache(
            ImmutableList<QuantifiableVariable> prefix) {
        if (prefix.isEmpty()) {
            return belowUpdateCacheEmptyPrefix;
        }
        return new BelowUpdateCache(prefix);
    }

    /**
     * @return <code>true</code> if the head operator of <code>t</code> is an update and
     *         <code>subtermIndex</code> is the number of the target subterm of the update
     */
    private boolean isUpdateTargetPos(Term t, int subtermIndex) {
        final Operator op = t.op();
        if (!(op instanceof UpdateApplication)) {
            return false;
        }

        return subtermIndex == UpdateApplication.targetPos();
    }

    /**
     * @return <code>true</code> if <code>op</code> is an operator below which we are caching
     */
    private boolean isAcceptedOperator(Operator op) {
        return op instanceof IfThenElse
                || (op instanceof Function && !(op instanceof Transformer))
                || op instanceof Junctor || op instanceof Equality || op instanceof Quantifier
                || op instanceof UpdateApplication || op instanceof Modality;
    }

    ////////////////////////////////////////////////////////////////////////////

    private class TopLevelCache extends PrefixTermTacletAppIndexCacheImpl {
        /**
         * the polarity of the positions this cache is responsible for: -1 for antecedent-like,
         * 1 for succedent-like, 0 for indefinite polarity
         */
        private final int polarity;

        protected TopLevelCache(ImmutableList<QuantifiableVariable> prefix, int polarity,
                Map<CacheKey, TermTacletAppIndex> cache) {
            super(prefix, cache);
            this.polarity = polarity;
        }

        @Override
        public ITermTacletAppIndexCache descend(Term t, int subtermIndex) {
            if (isUpdateTargetPos(t, subtermIndex)) {
                return getBelowUpdateCache(getExtendedPrefix(t, subtermIndex));
            }

            final Operator op = t.op();
            if (op instanceof Modality) {
                return getBelowProgCache(getExtendedPrefix(t, subtermIndex));
            }

            if (isAcceptedOperator(op)) {
                return getTopLevelCache(getExtendedPrefix(t, subtermIndex),
                    childPolarity(op, subtermIndex, polarity));
            }

            return noCache;
        }

        @Override
        protected String name() {
            return "TopLevelCache" + getPrefix() + "/" + polarity;
        }
    }

    ////////////////////////////////////////////////////////////////////////////

    private class BelowUpdateCache extends PrefixTermTacletAppIndexCache {
        public BelowUpdateCache(ImmutableList<QuantifiableVariable> prefix) {
            super(prefix);
        }

        @Override
        public ITermTacletAppIndexCache descend(Term t, int subtermIndex) {
            final Operator op = t.op();
            if (op instanceof Modality) {
                return getBelowProgCache(getExtendedPrefix(t, subtermIndex));
            }

            if (isAcceptedOperator(op)) {
                return getBelowUpdateCache(getExtendedPrefix(t, subtermIndex));
            }

            return noCache;
        }

        @Override
        public TermTacletAppIndex getIndexForTerm(Term t) {
            return null;
        }

        @Override
        public void putIndexForTerm(Term t, TermTacletAppIndex index) {}
    }

    ////////////////////////////////////////////////////////////////////////////

    private class BelowProgCache extends PrefixTermTacletAppIndexCacheImpl {
        protected BelowProgCache(ImmutableList<QuantifiableVariable> prefix,
                Map<CacheKey, TermTacletAppIndex> cache) {
            super(prefix, cache);
        }

        @Override
        public ITermTacletAppIndexCache descend(Term t, int subtermIndex) {
            if (isAcceptedOperator(t.op())) {
                return getBelowProgCache(getExtendedPrefix(t, subtermIndex));
            }

            return noCache;
        }

        @Override
        protected String name() {
            return "BelowProgCache" + getPrefix();
        }
    }

}
