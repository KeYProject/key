/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.PrefixTermTacletAppIndexCacheImpl.CacheKey;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Cache that is used for accelerating <code>TermTacletAppIndex</code>. Basically, this is a mapping
 * from terms to objects of <code>TermTacletAppIndex</code>, following the idea that the same
 * taclets will be applicable to an occurrence of the same term in different places.
 *
 * There are different categories of locations/areas in a term that have to be separated, because
 * different taclets could be applicable. These are:
 * <ul>
 * <li>Toplevel in the antecedent</li>
 * <li>Toplevel in the succedent</li>
 * <li>Non-toplevel, but not below updates or programs and not below "bad" operators that we do not
 * know (defined by <code>TermTacletAppIndexCacheSet.isAcceptedOperator</code>). In this case we
 * also have to distinguish different prefixes of a position, i.e., different sets of variables that
 * are bound above a position.</li>
 * <li>Below updates, but not below programs. We do not cache at all in such places.</li>
 * <li>Below programs. Again, we also have to distinguish different prefixes of a position.</li>
 * <li>Below other "bad" operators. We do not cache at all in such places.</li>
 * </ul>
 *
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
        public ITermTacletAppIndexCache descend(Term t, int subtermIndex) {
            return this;
        }

        public TermTacletAppIndex getIndexForTerm(Term t) {
            return null;
        }

        public void putIndexForTerm(Term t, TermTacletAppIndex index) {}
    };

    /**
     * the toplevel caches for the antecedent and the succedent. These are the starting points when
     * determining the cache for an arbitrary position
     */
    private final ITermTacletAppIndexCache antecCache;
    private final ITermTacletAppIndexCache succCache;

    /**
     * cache for locations that are not below updates, programs or in the scope of binders
     */
    private final ITermTacletAppIndexCache topLevelCacheEmptyPrefix;

    /**
     * caches for locations that are not below updates or programs, but in the scope of binders.
     * this is a mapping from <code>IList<QuantifiedVariable></code> to <code>TopLevelCache</code>
     */
    private final LRUCache<ImmutableList<QuantifiableVariable>, ITermTacletAppIndexCache> topLevelCaches =
        new LRUCache<>(
            MAX_CACHE_ENTRIES);

    /**
     * cache for locations that are below updates, but not below programs or in the scope of binders
     */
    private final ITermTacletAppIndexCache belowUpdateCacheEmptyPrefix =
        new BelowUpdateCache(ImmutableSLList.nil());

    /**
     * cache for locations that are below programs, but not in the scope of binders
     */
    private final ITermTacletAppIndexCache belowProgCacheEmptyPrefix;

    /**
     * caches for locations that are both below programs and in the scope of binders. this is a
     * mapping from <code>IList<QuantifiedVariable></code> to <code>BelowProgCache</code>
     */
    private final LRUCache<ImmutableList<QuantifiableVariable>, ITermTacletAppIndexCache> belowProgCaches =
        new LRUCache<>(
            MAX_CACHE_ENTRIES);

    private final Map<CacheKey, TermTacletAppIndex> cache;

    public TermTacletAppIndexCacheSet(Map<CacheKey, TermTacletAppIndex> cache) {
        assert cache != null;
        this.cache = cache;
        antecCache = new TopLevelCache(ImmutableSLList.nil(), cache);
        succCache = new TopLevelCache(ImmutableSLList.nil(), cache);
        topLevelCacheEmptyPrefix =
            new TopLevelCache(ImmutableSLList.nil(), cache);
        belowProgCacheEmptyPrefix =
            new BelowProgCache(ImmutableSLList.nil(), cache);
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
     * @return <code>true</code> iff <code>t</code> is a taclet that might possibly be cached by any
     *         of the caches of this set
     */
    public boolean isRelevantTaclet(Taclet t) {
        return t instanceof FindTaclet;
    }
    ////////////////////////////////////////////////////////////////////////////

    /**
     * @return the cache for locations that are not below updates or programs and in the scope of
     *         binders binding <code>prefix</code> (which might be empty)
     */
    private ITermTacletAppIndexCache getTopLevelCache(ImmutableList<QuantifiableVariable> prefix) {
        if (prefix.isEmpty()) {
            return topLevelCacheEmptyPrefix;
        }
        ITermTacletAppIndexCache res = topLevelCaches.get(prefix);
        if (res == null) {
            res = new TopLevelCache(prefix, cache);
            topLevelCaches.put(prefix, res);
        }
        return res;
    }

    /**
     * @return the cache for locations that are below programs and in the scope of binders binding
     *         <code>prefix</code> (which might be empty)
     */
    private ITermTacletAppIndexCache getBelowProgCache(ImmutableList<QuantifiableVariable> prefix) {
        if (prefix.isEmpty()) {
            return belowProgCacheEmptyPrefix;
        }
        ITermTacletAppIndexCache res = belowProgCaches.get(prefix);
        if (res == null) {
            res = new BelowProgCache(prefix, cache);
            belowProgCaches.put(prefix, res);
        }
        return res;
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
                || (op instanceof JFunction && !(op instanceof Transformer))
                || op instanceof Junctor || op instanceof Equality || op instanceof Quantifier
                || op instanceof UpdateApplication || op instanceof Modality;
    }

    ////////////////////////////////////////////////////////////////////////////

    private class TopLevelCache extends PrefixTermTacletAppIndexCacheImpl {
        protected TopLevelCache(ImmutableList<QuantifiableVariable> prefix,
                Map<CacheKey, TermTacletAppIndex> cache) {
            super(prefix, cache);
        }

        public ITermTacletAppIndexCache descend(Term t, int subtermIndex) {
            if (isUpdateTargetPos(t, subtermIndex)) {
                return getBelowUpdateCache(getExtendedPrefix(t, subtermIndex));
            }

            final Operator op = t.op();
            if (op instanceof Modality) {
                return getBelowProgCache(getExtendedPrefix(t, subtermIndex));
            }

            if (isAcceptedOperator(op)) {
                return getTopLevelCache(getExtendedPrefix(t, subtermIndex));
            }

            return noCache;
        }

        protected String name() {
            return "TopLevelCache" + getPrefix();
        }
    }

    ////////////////////////////////////////////////////////////////////////////

    private class BelowUpdateCache extends PrefixTermTacletAppIndexCache {
        public BelowUpdateCache(ImmutableList<QuantifiableVariable> prefix) {
            super(prefix);
        }

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

        public TermTacletAppIndex getIndexForTerm(Term t) {
            return null;
        }

        public void putIndexForTerm(Term t, TermTacletAppIndex index) {}
    }

    ////////////////////////////////////////////////////////////////////////////

    private class BelowProgCache extends PrefixTermTacletAppIndexCacheImpl {
        protected BelowProgCache(ImmutableList<QuantifiableVariable> prefix,
                Map<CacheKey, TermTacletAppIndex> cache) {
            super(prefix, cache);
        }

        public ITermTacletAppIndexCache descend(Term t, int subtermIndex) {
            if (isAcceptedOperator(t.op())) {
                return getBelowProgCache(getExtendedPrefix(t, subtermIndex));
            }

            return noCache;
        }

        protected String name() {
            return "BelowProgCache" + getPrefix();
        }
    }

}
