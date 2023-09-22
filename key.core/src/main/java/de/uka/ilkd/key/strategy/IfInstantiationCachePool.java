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
import de.uka.ilkd.key.rule.IfFormulaInstantiation;

import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableList;

/**
 * Direct-mapped cache of lists of formulas (potential instantiations of if-formulas of taclets)
 * that were modified after a certain point of time
 *
 * Hashmaps of the particular lists of formulas; the keys of the maps is the point of time that
 * separates old from new (modified) formulas
 *
 * Keys: Long Values: IList<IfFormulaInstantiation>
 */
public class IfInstantiationCachePool {

    public final LRUCache<Node, IfInstantiationCache> cacheMgr = new LRUCache<>(10);

    public IfInstantiationCache getCache(Node n) {
        IfInstantiationCache cache;
        synchronized (cacheMgr) {
            cache = cacheMgr.get(n);
        }

        if (cache != null) {
            return cache;
        }

        cache = new IfInstantiationCache();

        IfInstantiationCache cache2;
        synchronized (cacheMgr) {
            cache2 = cacheMgr.putIfAbsent(n, cache);
        }

        if (cache2 != null) {
            cache = cache2;
        }

        return cache;
    }

    public void releaseAll() {
        synchronized (cacheMgr) {
            cacheMgr.clear();
        }
    }

    public void release(Node n) {
        IfInstantiationCache cache = null;
        synchronized (cacheMgr) {
            cache = cacheMgr.remove(n);
        }
        if (cache != null) {
            cache.reset();
        }
    }

    public static class IfInstantiationCache {

        private final HashMap<Long, ImmutableList<IfFormulaInstantiation>> antecCache =
            new LinkedHashMap<>();
        private final HashMap<Long, ImmutableList<IfFormulaInstantiation>> succCache =
            new LinkedHashMap<>();

        private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
        private final ReadLock readLock = lock.readLock();
        private final WriteLock writeLock = lock.writeLock();

        public ImmutableList<IfFormulaInstantiation> get(boolean antec, Long key) {
            try {
                readLock.lock();
                final HashMap<Long, ImmutableList<IfFormulaInstantiation>> cache =
                    antec ? antecCache : succCache;
                return cache.get(key);
            } finally {
                readLock.unlock();
            }
        }

        public void put(boolean antec, Long key, ImmutableList<IfFormulaInstantiation> value) {
            final HashMap<Long, ImmutableList<IfFormulaInstantiation>> cache =
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
