/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.collection;

import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Tests {@link WeakValueInterner}: it must return the same canonical instance for equal keys, even
 * under concurrent access (the property that makes interned objects safe to compare with
 * {@code ==}).
 */
public class WeakValueInternerTest {

    @Test
    void sameKeyYieldsSameInstance() {
        WeakValueInterner<String, Object> interner = new WeakValueInterner<>();
        Object a = interner.intern("k", k -> new Object());
        Object b = interner.intern("k", k -> new Object());
        assertSame(a, b, "equal keys must intern to the same instance");
        Object c = interner.intern("other", k -> new Object());
        assertTrue(a != c, "different keys must intern to different instances");
    }

    @Test
    void concurrentInternNeverProducesDistinctInstancesForSameKey() throws Exception {
        final int threads = 16;
        final int keys = 500;
        final WeakValueInterner<Integer, Object> interner = new WeakValueInterner<>();
        // For each key, collect every instance any thread received. Identity holds iff each key
        // maps
        // to exactly one instance across all threads.
        final ConcurrentHashMap<Integer, Set<Object>> perKey = new ConcurrentHashMap<>();
        final CopyOnWriteArrayList<Throwable> failures = new CopyOnWriteArrayList<>();
        final CountDownLatch start = new CountDownLatch(1);
        final CountDownLatch done = new CountDownLatch(threads);

        for (int t = 0; t < threads; t++) {
            new Thread(() -> {
                try {
                    start.await();
                    for (int i = 0; i < keys; i++) {
                        Object v = interner.intern(i, k -> new Object());
                        perKey.computeIfAbsent(i, k -> ConcurrentHashMap.newKeySet()).add(v);
                    }
                } catch (Throwable th) {
                    failures.add(th);
                } finally {
                    done.countDown();
                }
            }).start();
        }
        start.countDown();
        assertTrue(done.await(30, TimeUnit.SECONDS), "interner threads did not finish");

        assertTrue(failures.isEmpty(), () -> "thread(s) failed: " + failures);
        assertEquals(keys, perKey.size());
        for (var entry : perKey.entrySet()) {
            assertEquals(1, entry.getValue().size(),
                "key " + entry.getKey() + " interned to more than one instance: "
                    + entry.getValue().size());
        }
    }
}
