/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicReference;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests for {@link StripedLruCache}, which backs the term interner used by every term creation
 * under
 * the multi-core prover. The two properties that matter for that use are checked explicitly: (1)
 * <em>equal keys map to the same segment</em>, so two distinct-but-equal keys see one another's
 * entry (a correct interner); and (2) it stays consistent and exception-free under heavy concurrent
 * access.
 *
 * @author Claude (KeY multithreading effort)
 */
public class StripedLruCacheTest {

    @Test
    void getReturnsWhatWasPut() {
        StripedLruCache<String, Integer> c = new StripedLruCache<>(64, 8);
        assertNull(c.get("a"));
        c.put("a", 1);
        assertEquals(1, c.get("a"));
    }

    /** The interner-critical property: a distinct-but-equal key hits the same entry. */
    @Test
    void equalButDistinctKeysShareAnEntry() {
        StripedLruCache<String, String> c = new StripedLruCache<>(64, 16);
        String key1 = new String("term"); // distinct identity ...
        String key2 = new String("term"); // ... but equal and same hashCode
        assertNotSameIdentity(key1, key2);
        c.put(key1, "value");
        assertEquals("value", c.get(key2), "equal keys must map to the same segment");
    }

    @Test
    void computeIfAbsentComputesOnceThenCaches() {
        StripedLruCache<String, String> c = new StripedLruCache<>(64, 8);
        int[] calls = { 0 };
        String v1 = c.computeIfAbsent("k", k -> {
            calls[0]++;
            return "v";
        });
        String v2 = c.computeIfAbsent("k", k -> {
            calls[0]++;
            return "v";
        });
        assertEquals("v", v1);
        assertSame(v1, v2);
        assertEquals(1, calls[0], "second computeIfAbsent must hit the cache");
    }

    @Test
    void totalCapacityIsBounded() {
        // 16 entries over 8 stripes -> 2 per stripe; inserting 1000 keys must never exceed
        // capacity.
        StripedLruCache<Integer, Integer> c = new StripedLruCache<>(16, 8);
        for (int i = 0; i < 1000; i++) {
            c.put(i, i);
        }
        assertTrue(c.size() <= 16, "size " + c.size() + " exceeded the bound");
    }

    /**
     * Under heavy concurrency on a shared key set (no eviction: cache is big enough), every key
     * must
     * keep its single value -- the cache never returns a wrong or corrupt entry, and never throws.
     */
    @Test
    void concurrentAccessStaysConsistent() throws Exception {
        final int keys = 256;
        final int threads = 16;
        final int opsPerThread = 50_000;
        // Big enough to hold every key without eviction, so a wrong answer can only be a race bug.
        StripedLruCache<Integer, String> c = new StripedLruCache<>(keys * 4, 32);

        ExecutorService pool = Executors.newFixedThreadPool(threads);
        AtomicReference<Throwable> failure = new AtomicReference<>();
        var barrier = new CyclicBarrier(threads);
        var futures = new java.util.ArrayList<Future<?>>();
        for (int t = 0; t < threads; t++) {
            final long seed = t;
            futures.add(pool.submit(() -> {
                try {
                    barrier.await();
                    java.util.Random rnd = new java.util.Random(seed);
                    for (int i = 0; i < opsPerThread; i++) {
                        int k = rnd.nextInt(keys);
                        String expected = "v" + k;
                        String got = c.computeIfAbsent(k, kk -> "v" + kk);
                        if (!expected.equals(got)) {
                            throw new AssertionError("key " + k + " -> " + got);
                        }
                        String peek = c.get(k);
                        if (peek != null && !expected.equals(peek)) {
                            throw new AssertionError("stale get for " + k + " -> " + peek);
                        }
                    }
                } catch (Throwable e) {
                    failure.compareAndSet(null, e);
                }
            }));
        }
        for (Future<?> f : futures) {
            f.get(60, TimeUnit.SECONDS);
        }
        pool.shutdownNow();
        if (failure.get() != null) {
            throw new AssertionError("concurrent inconsistency", failure.get());
        }
    }

    private static void assertNotSameIdentity(Object a, Object b) {
        assertTrue(a != b && a.equals(b) && a.hashCode() == b.hashCode(),
            "test precondition: equal, same-hash, distinct-identity keys");
    }
}
