/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.List;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Concurrency and bound tests for {@link ConcurrentLruCache} and {@link StripedLruCache}.
 *
 * <p>
 * The per-test timeout turns a deadlock or livelock regression in the caches into a test FAILURE
 * instead of an unbounded {@code Thread.join()} hanging the whole CI run. The tests finish in
 * seconds; the cap is deliberately generous for slow CI machines.
 */
@Timeout(value = 5, unit = TimeUnit.MINUTES)
public class LruCacheConcurrencyTest {

    private static final int THREADS = 16;
    private static final int KEYS = 2000;
    private static final int ITERS = 50;

    /** The exact cache must stay consistent and honour its size bound under heavy concurrency. */
    @Test
    public void concurrentLruCacheStaysConsistentAndBounded() throws Exception {
        final int cap = 256;
        final ConcurrentLruCache<Integer, Integer> cache = new ConcurrentLruCache<>(cap);
        hammer(cache::get, cache::put);
        assertTrue(cache.size() <= cap, "exact cache exceeded its capacity: " + cache.size());
        // every value present must equal its key's square (the only thing we ever stored)
        synchronized (cache.mutex()) {
            for (var e : cache.entrySet()) {
                assertEquals(e.getKey() * e.getKey(), e.getValue());
            }
        }
    }

    /**
     * The striped cache must stay consistent and honour its total bound under heavy concurrency.
     */
    @Test
    public void stripedLruCacheStaysConsistentAndBounded() throws Exception {
        final int cap = 256;
        final StripedLruCache<Integer, Integer> cache = new StripedLruCache<>(cap, 8);
        hammer(cache::get, cache::put);
        // per-segment rounding lets the total slightly exceed cap; it must stay hard-bounded though
        assertTrue(cache.size() <= cap + 8, "striped cache grew unbounded: " + cache.size());
    }

    /** computeIfAbsent must call the factory exactly once per key even under contention. */
    @Test
    public void stripedComputeIfAbsentIsAtomicPerKey() throws Exception {
        final StripedLruCache<Integer, Integer> cache = new StripedLruCache<>(KEYS * 2, 16);
        final ConcurrentHashMap<Integer, AtomicInteger> factoryCalls = new ConcurrentHashMap<>();
        final CyclicBarrier barrier = new CyclicBarrier(THREADS);
        final List<Throwable> failures = new CopyOnWriteArrayList<>();
        final Thread[] ts = new Thread[THREADS];
        for (int t = 0; t < THREADS; t++) {
            ts[t] = new Thread(() -> {
                try {
                    barrier.await();
                    for (int k = 0; k < KEYS; k++) {
                        final int key = k;
                        int v = cache.computeIfAbsent(key, kk -> {
                            factoryCalls.computeIfAbsent(kk, x -> new AtomicInteger())
                                    .incrementAndGet();
                            return kk * kk;
                        });
                        assertEquals(key * key, v);
                    }
                } catch (Throwable th) {
                    failures.add(th);
                }
            });
        }
        for (Thread th : ts) {
            th.start();
        }
        for (Thread th : ts) {
            th.join();
        }
        assertTrue(failures.isEmpty(), () -> "worker(s) threw: " + failures);
        // capacity is generous (no eviction), so each key is computed exactly once despite races
        for (var e : factoryCalls.entrySet()) {
            assertEquals(1, e.getValue().get(), "key " + e.getKey() + " computed more than once");
        }
    }

    /**
     * The exact cache must evict in true least-recently-used order, and a {@code get} must count as
     * a use. This is the property that makes {@link ConcurrentLruCache} (rather than the striped
     * cache) mandatory for the eviction-sensitive caches, so it is worth pinning.
     */
    @Test
    public void concurrentLruCacheEvictsLeastRecentlyUsed() {
        final ConcurrentLruCache<Integer, Integer> cache = new ConcurrentLruCache<>(3);
        cache.put(1, 1);
        cache.put(2, 2);
        cache.put(3, 3);
        // touch 1, so the least-recently-used entry is now 2
        assertEquals(1, Objects.requireNonNull(cache.get(1)));
        // inserting a fourth entry must evict 2 (the LRU), keeping 1, 3 and 4
        cache.put(4, 4);
        assertNull(cache.get(2), "least-recently-used entry was not evicted");
        assertEquals(1, Objects.requireNonNull(cache.get(1)));
        assertEquals(3, Objects.requireNonNull(cache.get(3)));
        assertEquals(4, Objects.requireNonNull(cache.get(4)));
        assertTrue(cache.size() <= 3, "exact cache exceeded its capacity");
    }

    /**
     * computeIfAbsent on the exact cache must call the factory exactly once per key under races.
     */
    @Test
    public void concurrentLruCacheComputeIfAbsentIsAtomicPerKey() throws Exception {
        final ConcurrentLruCache<Integer, Integer> cache = new ConcurrentLruCache<>(KEYS * 2);
        final ConcurrentHashMap<Integer, AtomicInteger> factoryCalls = new ConcurrentHashMap<>();
        final CyclicBarrier barrier = new CyclicBarrier(THREADS);
        final List<Throwable> failures = new CopyOnWriteArrayList<>();
        final Thread[] ts = new Thread[THREADS];
        for (int t = 0; t < THREADS; t++) {
            ts[t] = new Thread(() -> {
                try {
                    barrier.await();
                    for (int k = 0; k < KEYS; k++) {
                        int v = Objects.requireNonNull(cache.computeIfAbsent(k, kk -> {
                            factoryCalls.computeIfAbsent(kk, x -> new AtomicInteger())
                                    .incrementAndGet();
                            return kk * kk;
                        }));
                        assertEquals(k * k, v);
                    }
                } catch (Throwable th) {
                    failures.add(th);
                }
            });
        }
        for (Thread th : ts) {
            th.start();
        }
        for (Thread th : ts) {
            th.join();
        }
        assertTrue(failures.isEmpty(), () -> "worker(s) threw: " + failures);
        for (var e : factoryCalls.entrySet()) {
            assertEquals(1, e.getValue().get(), "key " + e.getKey() + " computed more than once");
        }
    }

    /** Sanity: a miss returns null, a stored entry is retrievable (single-threaded). */
    @Test
    public void basicGetPut() {
        ConcurrentLruCache<String, String> exact = new ConcurrentLruCache<>(4);
        StripedLruCache<String, String> striped = new StripedLruCache<>(4, 4);
        assertNull(exact.get("x"));
        assertNull(striped.get("x"));
        exact.put("x", "1");
        striped.put("x", "1");
        assertEquals("1", exact.get("x"));
        assertEquals("1", striped.get("x"));
    }

    private interface Getter {
        @Nullable
        Integer get(Integer key);
    }

    private interface Putter {
        void put(Integer key, Integer value);
    }

    private static void hammer(Getter get, Putter put) throws Exception {
        final CyclicBarrier barrier = new CyclicBarrier(THREADS);
        final List<Throwable> failures = new CopyOnWriteArrayList<>();
        final Thread[] ts = new Thread[THREADS];
        for (int t = 0; t < THREADS; t++) {
            ts[t] = new Thread(() -> {
                try {
                    barrier.await();
                    for (int it = 0; it < ITERS; it++) {
                        for (int k = 0; k < KEYS; k++) {
                            put.put(k, k * k);
                            Integer v = get.get(k);
                            if (v != null) {
                                assertEquals(k * k, v.intValue());
                            }
                        }
                    }
                } catch (Throwable th) {
                    failures.add(th);
                }
            });
        }
        for (Thread th : ts) {
            th.start();
        }
        for (Thread th : ts) {
            th.join();
        }
        assertTrue(failures.isEmpty(), () -> "worker(s) threw: " + failures);
    }
}
