/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.Function;

import org.jspecify.annotations.Nullable;

/**
 * A bounded cache that several threads can use at the same time, built for speed under heavy
 * concurrent use.
 *
 * <p>
 * Vocabulary, in one paragraph: a <em>cache</em> stores results of a computation so they do not
 * have to be computed again; <em>bounded</em> means it holds at most a fixed number of entries;
 * when a part of it is full, the entry that has not been used for the longest time is thrown out
 * (<em>least recently used</em>, LRU, <em>eviction</em>); <em>thread-safe</em> means several
 * threads may call any method at any time without corrupting the cache -- important in KeY
 * because the multi-core prover runs proof search on several worker threads that all see the same
 * cache.
 *
 * <p>
 * A cache with one single lock (like {@link ConcurrentLruCache}) makes every thread wait in line,
 * even when they ask for completely different keys. This class avoids that by <em>striping</em>:
 * the keys are split over several independent segments, each with its own lock and its own small
 * LRU map. A thread only locks the one segment its key belongs to, so threads working on
 * different segments never wait for each other.
 *
 * <p>
 * The price of striping: there is no single LRU order over the whole cache, only one per segment.
 * So <em>which</em> entry gets evicted next is not exactly predictable from the outside. That is
 * harmless exactly when the cached value is a <em>pure function of the key</em> -- same key,
 * always the same value (example from KeY: "does this term contain a modality?"). Then an early
 * eviction only means the same value is computed once more; no result ever changes. It is NOT
 * harmless when the value depends on when it was first stored -- for such caches the eviction
 * order can change results, and {@link ConcurrentLruCache} (exact, single-lock) must be used.
 * One-question test: <em>"if this entry were thrown away and computed again later, could the new
 * value be different?"</em> No &rarr; this class. Yes &rarr; {@link ConcurrentLruCache}.
 *
 * <p>
 * The total capacity is still hard-bounded (each of the {@code stripes} segments holds at most
 * {@code ceil(maxEntries / stripes)} entries), so the cache cannot grow without limit.
 *
 * @param <K> the key type
 * @param <V> the value type
 */
public final class StripedLruCache<K, V> {

    private final EvictingMap<K, V>[] segments;
    private final Object[] locks;
    private final int mask;

    /**
     * Access-ordered, size-bounded map used as one striped segment. Not thread-safe on its own --
     * {@link StripedLruCache} guards every access with the segment's lock. Kept private so no
     * non-thread-safe LRU map leaks into the rest of the code base (use {@link ConcurrentLruCache}
     * or {@link StripedLruCache} instead).
     */
    private static final class EvictingMap<K, V> extends LinkedHashMap<K, V> {
        private final int maxEntries;

        EvictingMap(int maxEntries) {
            super(maxEntries + 1, 1.0F, true);
            this.maxEntries = maxEntries;
        }

        @Override
        protected boolean removeEldestEntry(Map.Entry<K, V> eldest) {
            return size() > maxEntries;
        }
    }

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
        this.segments = new EvictingMap[n];
        this.locks = new Object[n];
        final int perSegment = Math.max(1, (maxEntries + n - 1) / n);
        for (int i = 0; i < n; i++) {
            segments[i] = new EvictingMap<>(perSegment);
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
