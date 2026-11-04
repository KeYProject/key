/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.util;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import org.jspecify.annotations.Nullable;

/**
 * A bounded cache whose reads take no lock and, on a hit, write at most once per generation.
 *
 * <p>
 * One {@link ConcurrentHashMap} holds the entries. Each entry records the generation of its last
 * use. A read is one map lookup and a comparison of that generation with the current one; the
 * entry's generation is written only when it differs. An insert goes into the map and counts
 * towards the next sweep. The sweep starts a new generation and removes every entry that was
 * not used in the generation that just ended, so an entry in use is never removed and an unused
 * one lives for one to two generations. If the entries in use alone exceed the bound, the sweep
 * removes entries in table order, in use or not, down to half the bound. The thread whose insert
 * reaches the limit sweeps; the other threads keep reading and inserting meanwhile. The number
 * of inserts between two sweeps is the room left after the last sweep, at least an eighth of the
 * bound.
 *
 * <p>
 * The cache may drop any entry at any time (an entry used while a sweep runs can be removed), so
 * only values that a recomputation reproduces may be cached. The map never holds more than the
 * bound plus an eighth: an insert that finds it that full (the size after the last sweep plus
 * the inserts since) is refused and sweeps instead, so threads that re-insert faster than a
 * sweep removes cannot grow it.
 *
 * <p>
 * {@link ConcurrentLruCache} keeps an exact least-recently-used order behind one lock;
 * {@link StripedLruCache} keeps one such order per segment behind the segment's lock. Both write
 * on every read. This class is for caches that the multi-core prover's workers read far more
 * often than they insert into.
 *
 * @param <K> the key type
 * @param <V> the value type
 */
public final class GenerationalCache<K, V> {

    /** A cached value with the generation of its last use. */
    private static final class Entry<V> {
        final V value;
        /**
         * Generation of the last use. A plain field: a stale read costs one repeated write or
         * one early eviction, never a wrong value.
         */
        int generation;

        Entry(V value, int generation) {
            this.value = value;
            this.generation = generation;
        }
    }

    private final ConcurrentHashMap<K, Entry<V>> map;
    /** The bound on the number of entries. */
    private final int capacity;
    /** The room a sweep leaves free at least, and the fewest inserts between two sweeps. */
    private final int minimumRoom;
    /** The current generation; a sweep starts the next one. */
    private volatile int generation;
    /** Inserts since the last sweep. */
    private final AtomicInteger inserts = new AtomicInteger();
    /** The number of entries when the last sweep ended. */
    private volatile int sizeAfterSweep;
    /** The insert count at which the next sweep runs. */
    private volatile int limit;
    /** Set while a thread sweeps, so that no second thread sweeps or waits. */
    private final AtomicBoolean sweeping = new AtomicBoolean();

    /**
     * Creates the cache.
     *
     * @param capacity the bound on the number of entries
     */
    public GenerationalCache(int capacity) {
        this.capacity = Math.max(8, capacity);
        this.minimumRoom = Math.max(1, this.capacity / 8);
        this.map = new ConcurrentHashMap<>(2 * this.capacity);
        // The first sweep ends a generation in which every entry was inserted, so it can remove
        // nothing by use; running it at half the bound keeps its second pass out of it.
        this.limit = this.capacity / 2;
    }

    /**
     * @param key the key to look up (non-null)
     * @return the cached value, or {@code null} if absent
     */
    public @Nullable V get(K key) {
        final Entry<V> entry = map.get(key);
        if (entry == null) {
            return null;
        }
        final int current = generation;
        if (entry.generation != current) {
            entry.generation = current;
        }
        return entry.value;
    }

    /**
     * Stores {@code value} unless a value is cached for {@code key}, in which case that value
     * counts as used and is returned.
     *
     * @param key the key to store under (non-null)
     * @param value the value to cache when the key is absent
     * @return the previously cached value, or {@code null} if {@code value} was stored
     */
    public @Nullable V putIfAbsent(K key, V value) {
        final int current = generation;
        if (sizeAfterSweep + inserts.get() >= capacity + minimumRoom) {
            // Full beyond the slack: do not insert, make room. The caller keeps its value.
            sweep(true);
            final Entry<V> present = map.get(key);
            if (present == null) {
                return null;
            }
            if (present.generation != current) {
                present.generation = current;
            }
            return present.value;
        }
        final Entry<V> previous = map.putIfAbsent(key, new Entry<>(value, current));
        if (previous != null) {
            if (previous.generation != current) {
                previous.generation = current;
            }
            return previous.value;
        }
        if (inserts.incrementAndGet() >= limit) {
            sweep(false);
        }
        return null;
    }

    /**
     * Starts the next generation and removes the entries not used in the one that ended. Runs
     * on the inserting thread; a second thread that reaches the limit meanwhile returns at once.
     *
     * @param forced {@code true} when the map is full beyond the slack, which sweeps even if the
     *        insert count has not reached the limit
     */
    private void sweep(boolean forced) {
        if (!sweeping.compareAndSet(false, true)) {
            return;
        }
        try {
            if (!forced && inserts.get() < limit) {
                return;
            }
            final int ended = generation;
            generation = ended + 1;
            map.forEach((key, entry) -> {
                if (entry.generation < ended) {
                    map.remove(key, entry);
                }
            });
            if (map.size() > capacity - minimumRoom) {
                // The entries in use exceed the bound: drop entries in table order, in use or
                // not, down to half the bound, so that the next sweep is half a bound of
                // inserts away. Readers stamp entries meanwhile, so the stamp decides nothing here.
                final int target = capacity / 2;
                for (Map.Entry<K, Entry<V>> e : map.entrySet()) {
                    if (map.size() <= target) {
                        break;
                    }
                    map.remove(e.getKey(), e.getValue());
                }
            }
            final int size = map.size();
            limit = Math.max(minimumRoom, capacity - size);
            sizeAfterSweep = size;
            inserts.set(0);
        } finally {
            sweeping.set(false);
        }
    }

    /** @return the number of entries (approximate under concurrency) */
    public int size() {
        return map.size();
    }

    /** @return the generations started so far */
    public int generation() {
        return generation;
    }

    /**
     * Removes the entry of {@code key}, if there is one; a later lookup of the key misses.
     *
     * @param key the key whose entry is removed
     * @return the removed value, or {@code null} if there was none
     */
    public @Nullable V remove(K key) {
        final Entry<V> entry = map.remove(key);
        return entry == null ? null : entry.value;
    }

    /** Removes all entries. */
    public void clear() {
        map.clear();
        inserts.set(0);
        sizeAfterSweep = 0;
        limit = capacity;
    }
}
