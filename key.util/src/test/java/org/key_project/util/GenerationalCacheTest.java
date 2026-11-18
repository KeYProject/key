/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.util;

import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CyclicBarrier;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class GenerationalCacheTest {

    @Test
    public void getReturnsWhatWasPut() {
        final GenerationalCache<String, String> cache = new GenerationalCache<>(8);
        assertNull(cache.putIfAbsent("a", "va"));
        assertEquals("va", cache.get("a"));
        assertNull(cache.get("b"));
    }

    @Test
    public void putIfAbsentKeepsTheFirstValue() {
        final GenerationalCache<String, String> cache = new GenerationalCache<>(8);
        assertNull(cache.putIfAbsent("k", "first"));
        final String second = cache.putIfAbsent("k", "second");
        assertNotNull(second);
        assertSame("first", second);
        final String got = cache.get("k");
        assertNotNull(got);
        assertSame("first", got);
    }

    @Test
    public void removeReturnsRemovedValue() {
        final GenerationalCache<String, String> cache = new GenerationalCache<>(8);
        assertNull(cache.remove("a"));
        assertNull(cache.putIfAbsent("a", "va"));
        final String removed = cache.remove("a");
        assertNotNull(removed);
        assertEquals("va", removed);
        assertNull(cache.get("a"));
        assertNull(cache.remove("a"));
    }

    @Test
    public void usedEntrySurvivesSweeps() {
        final int cap = 64;
        final GenerationalCache<Integer, Integer> cache = new GenerationalCache<>(cap);
        cache.putIfAbsent(-1, -1);
        for (int i = 0; i < 8 * cap; i++) {
            cache.putIfAbsent(i, i);
            if (i % 8 == 0) {
                final Integer hot = cache.get(-1);
                assertNotNull(hot, "the entry in use was removed at insert " + i);
                assertEquals(-1, hot);
            }
        }
        assertTrue(cache.generation() >= 4, "the loop should have run several sweeps");
        final Integer hot = cache.get(-1);
        assertNotNull(hot);
        assertEquals(-1, hot);
    }

    @Test
    public void unusedEntryIsRemovedAfterTwoSweeps() {
        final int cap = 64;
        final GenerationalCache<Integer, Integer> cache = new GenerationalCache<>(cap);
        cache.putIfAbsent(-1, -1);
        int i = 0;
        while (cache.generation() < 3) {
            cache.putIfAbsent(i, i);
            i++;
        }
        assertNull(cache.get(-1), "an unused entry survived three sweeps");
    }

    @Test
    public void entriesStayBounded() {
        final int cap = 64;
        final GenerationalCache<Integer, Integer> cache = new GenerationalCache<>(cap);
        for (int i = 0; i < 100 * cap; i++) {
            cache.putIfAbsent(i, i);
            assertTrue(cache.size() <= cap, "size " + cache.size() + " after insert " + i);
        }
    }

    @Test
    public void concurrentUseStaysConsistent() throws Exception {
        final int cap = 256;
        final int keys = 1000;
        final int threads = 8;
        final GenerationalCache<Integer, Integer> cache = new GenerationalCache<>(cap);
        final CyclicBarrier barrier = new CyclicBarrier(threads);
        final List<Throwable> failures = new CopyOnWriteArrayList<>();
        final Thread[] ts = new Thread[threads];
        for (int t = 0; t < threads; t++) {
            final int seed = t;
            ts[t] = new Thread(() -> {
                try {
                    barrier.await();
                    for (int n = 0; n < 50_000; n++) {
                        final int key = (n * 7919 + seed * 104_729) % keys;
                        Integer v = cache.get(key);
                        if (v == null) {
                            final Integer prev = cache.putIfAbsent(key, key * key);
                            v = prev != null ? prev : key * key;
                        }
                        assertEquals(key * key, v);
                    }
                } catch (Throwable th) {
                    failures.add(th);
                }
            });
            ts[t].start();
        }
        for (Thread t : ts) {
            t.join();
        }
        assertTrue(failures.isEmpty(), "failures: " + failures);
        assertTrue(cache.size() <= 2 * cap, "size " + cache.size());
    }
}
