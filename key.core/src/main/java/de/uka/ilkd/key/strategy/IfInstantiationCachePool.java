/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.ReadLock;
import java.util.concurrent.locks.ReentrantReadWriteLock.WriteLock;

import de.uka.ilkd.key.proof.Node;

import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.util.ConcurrentLruCache;
import org.key_project.util.collection.ImmutableArray;

/**
 * Direct-mapped cache of lists of formulas (potential instantiations of if-formulas of taclets)
 * that were modified after a certain point of time
 * <p>
 * Hashmaps of the particular lists of formulas; the keys of the maps is the point of time that
 * separates old from new (modified) formulas
 * <p>
 * Keys: Long Values: IList<IfFormulaInstantiation>
 */
public class IfInstantiationCachePool {

    /**
     * Capacity of the per-proof, {@link Node}-keyed cache of assumes-instantiation results.
     * <p>
     * The cached value is a pure function of {@code (node, antec, age)} (the formulas modified
     * since a given age on that node's sequent), so eviction only affects the hit rate, never the
     * computed instantiations -- a hit returns exactly what a miss recomputes. Under multi-threaded
     * proof search up to (worker count) distinct goal nodes are instantiated concurrently, so the
     * old single-threaded value 10 evicted entries still in use for other in-flight goals. 64 sits
     * comfortably above realistic worker/concurrent-open-goal counts while keeping the map tiny
     * (each entry is one small {@link AssumesInstantiationCache}).
     */
    private static final int CACHE_CAPACITY = 64;

    public final ConcurrentLruCache<Node, AssumesInstantiationCache> cacheMgr =
        new ConcurrentLruCache<>(CACHE_CAPACITY);

    public AssumesInstantiationCache getCache(Node n) {
        // cacheMgr is a ConcurrentLruCache; get/putIfAbsent/clear/remove are individually atomic,
        // so no external synchronization is needed. The create-then-putIfAbsent idiom below already
        // resolves a concurrent-miss race (the loser adopts the winner's cache via the return).
        AssumesInstantiationCache cache = cacheMgr.get(n);
        if (cache != null) {
            return cache;
        }

        cache = new AssumesInstantiationCache();
        AssumesInstantiationCache cache2 = cacheMgr.putIfAbsent(n, cache);
        if (cache2 != null) {
            cache = cache2;
        }
        return cache;
    }

    public void releaseAll() {
        cacheMgr.clear();
    }

    public void release(Node n) {
        AssumesInstantiationCache cache = cacheMgr.remove(n);
        if (cache != null) {
            cache.reset();
        }
    }

    public static class AssumesInstantiationCache {

        private final HashMap<Long, ImmutableArray<AssumesFormulaInstantiation>> antecCache =
            new LinkedHashMap<>();
        private final HashMap<Long, ImmutableArray<AssumesFormulaInstantiation>> succCache =
            new LinkedHashMap<>();

        private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
        private final ReadLock readLock = lock.readLock();
        private final WriteLock writeLock = lock.writeLock();

        public ImmutableArray<AssumesFormulaInstantiation> get(boolean antec, Long key) {
            try {
                readLock.lock();
                final HashMap<Long, ImmutableArray<AssumesFormulaInstantiation>> cache =
                    antec ? antecCache : succCache;
                return cache.get(key);
            } finally {
                readLock.unlock();
            }
        }

        public void put(boolean antec, Long key,
                ImmutableArray<AssumesFormulaInstantiation> value) {
            final HashMap<Long, ImmutableArray<AssumesFormulaInstantiation>> cache =
                antec ? antecCache : succCache;
            try {
                writeLock.lock();
                cache.put(key, value);
            } finally {
                writeLock.unlock();
            }
        }

        private void reset() {
            try {
                writeLock.lock();
                antecCache.clear();
                succCache.clear();
            } finally {
                writeLock.unlock();
            }
        }
    }
}
