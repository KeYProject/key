/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.function.Function;

import org.jspecify.annotations.Nullable;

/**
 * A thread-safe, bounded LRU cache that reduces lock contention by <em>striping</em>: keys are
 * partitioned into independently locked segments, each a small exact {@link LRUCache}. An operation
 * locks only the one segment its key maps to, so concurrent workers touching different segments do
 * not block one another.
 *
 * <p>
 * The trade-off is that eviction is exact only <em>within</em> a segment, not globally: the
 * least-recently-used entry of the whole cache is not necessarily the next evicted. This is sound
 * only for <em>pure</em> caches, i.e. caches whose value is a function of the key alone, so that
 * eviction can only force a recomputation of the same value and never changes a result. Do not use
 * it for caches whose value depends on when it was first computed (use {@link ConcurrentLruCache}
 * for those).
 *
 * <p>
 * The total capacity is still hard-bounded (each of the {@code stripes} segments holds at most
 * {@code ceil(maxEntries / stripes)} entries), so the cache cannot grow without limit.
 *
 * @param <K> the key type
 * @param <V> the value type
 */
public final class StripedLruCache<K, V> {

    private final LRUCache<K, V>[] segments;
    private final Object[] locks;
    private final int mask;

    /**
     * Creates a striped cache holding at most about {@code maxEntries} entries in total, split over
     * {@code stripes} independently locked segments (rounded up to a power of two).
     *
     * @param maxEntries the approximate total capacity (across all segments)
     * @param stripes the desired number of segments; rounded up to the next power of two, min 1
     */
    @SuppressWarnings("unchecked")
    public StripedLruCache(int maxEntries, int stripes) {
        int n = 1;
        while (n < stripes) {
            n <<= 1;
        }
        this.mask = n - 1;
        this.segments = new LRUCache[n];
        this.locks = new Object[n];
        final int perSegment = Math.max(1, (maxEntries + n - 1) / n);
        for (int i = 0; i < n; i++) {
            segments[i] = new LRUCache<>(perSegment);
            locks[i] = new Object();
        }
    }

    /**
     * Spreads the hash so that the low bits used for striping are well distributed (mirrors the
     * spreading {@code ConcurrentHashMap} applies).
     */
    private int segmentFor(Object key) {
        int h = key.hashCode();
        h ^= (h >>> 16);
        return h & mask;
    }

    /**
     * @param key the key to look up (non-null)
     * @return the cached value, or {@code null} if absent
     */
    public @Nullable V get(K key) {
        final int i = segmentFor(key);
        synchronized (locks[i]) {
            return segments[i].get(key);
        }
    }

    /**
     * @param key the key to store under (non-null)
     * @param value the value to cache
     */
    public void put(K key, V value) {
        final int i = segmentFor(key);
        synchronized (locks[i]) {
            segments[i].put(key, value);
        }
    }

    /**
     * Returns the cached value for {@code key}, computing and storing it via
     * {@code mappingFunction}
     * if absent. The computation runs while holding the key's segment lock; keep it short and free
     * of calls back into this cache to avoid contention.
     *
     * @param key the key (non-null)
     * @param mappingFunction computes the value when absent
     * @return the cached or freshly computed value
     */
    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        final int i = segmentFor(key);
        synchronized (locks[i]) {
            @Nullable
            V value = segments[i].get(key);
            if (value == null) {
                value = mappingFunction.apply(key);
                segments[i].put(key, value);
            }
            return value;
        }
    }

    /** Removes all entries from every segment. */
    public void clear() {
        for (int i = 0; i < segments.length; i++) {
            synchronized (locks[i]) {
                segments[i].clear();
            }
        }
    }

    /**
     * @return the total number of entries currently held across all segments
     */
    public int size() {
        int total = 0;
        for (int i = 0; i < segments.length; i++) {
            synchronized (locks[i]) {
                total += segments[i].size();
            }
        }
        return total;
    }
}
