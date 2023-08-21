/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The abstract superclass of caches for taclet app indexes that are implemented using a common
 * backend <code>LRUCache</code> (the backend is stored in <code>TermTacletAppIndexCacheSet</code>).
 * The backend is accessed in a way that guarantees that two distinct instances of this class never
 * interfere, by choosing cache keys that are specific for a particular instance of
 * <code>PrefixTermTacletAppIndexCacheImpl</code> and cannot be created by other instances. This
 * ensures that it is safe to use one instance of <code>LRUCache</code> for many instances of
 * <code>PrefixTermTacletAppIndexCacheImpl</code> (different proofs, different proof branches,
 * different locations).
 */
public abstract class PrefixTermTacletAppIndexCacheImpl extends PrefixTermTacletAppIndexCache {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(PrefixTermTacletAppIndexCacheImpl.class);

    private final Map<CacheKey, TermTacletAppIndex> cache;

    protected PrefixTermTacletAppIndexCacheImpl(ImmutableList<QuantifiableVariable> prefix,
            Map<CacheKey, TermTacletAppIndex> cache) {
        super(prefix);
        this.cache = cache;
    }

    public TermTacletAppIndex getIndexForTerm(Term t) {
        return cache.get(getQueryKey(t));
    }

    private int hits = 0;
    private int total = 0;

    @SuppressWarnings("unused")
    private void countAccess(boolean hit) {
        ++total;
        if (hit) {
            ++hits;
        }
        if (total % 1000 == 0 && total != 0) {
            LOGGER.info("{} {}, size {}: {}", name(), hashCode(), cache.size(),
                ((double) hits) / (double) total);
        }
    }

    public void putIndexForTerm(Term t, TermTacletAppIndex index) {
        cache.put(getNewKey(t), index);
    }

    /**
     * Only used for debugging purposes
     */
    protected abstract String name();

    /**
     * @return a freshly created key for the term <code>t</code> that can be stored in the
     *         <code>cache</code>
     */
    private CacheKey getNewKey(Term t) {
        return new CacheKey(this, t);
    }

    /**
     * @return a key for the term <code>t</code> that can be used for cache queries. Calling this
     *         method twice will return the same object (with different attribute values), i.e., the
     *         result is not supposed to be stored anywhere
     */
    private CacheKey getQueryKey(Term t) {
        queryCacheKey.analysedTerm = t;
        return queryCacheKey;
    }

    private final CacheKey queryCacheKey = new CacheKey(this, null);

    public static final class CacheKey {
        private final PrefixTermTacletAppIndexCacheImpl parent;
        public Term analysedTerm;

        public CacheKey(PrefixTermTacletAppIndexCacheImpl parent, Term analysedTerm) {
            this.parent = parent;
            this.analysedTerm = analysedTerm;
        }

        public boolean equals(Object obj) {
            if (!(obj instanceof CacheKey)) {
                return false;
            }

            final CacheKey objKey = (CacheKey) obj;
            return parent == objKey.parent && analysedTerm.equals(objKey.analysedTerm);
        }

        public int hashCode() {
            return parent.hashCode() * 3784831 + analysedTerm.hashCode();
        }
    }
}
