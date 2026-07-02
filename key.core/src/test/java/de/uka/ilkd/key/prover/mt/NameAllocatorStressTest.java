/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import de.uka.ilkd.key.prover.impl.ParallelNameAllocator;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The Phase-2 acceptance check (multithreading effort): hammering {@link ParallelNameAllocator}
 * from many threads must never produce a duplicate name and must be per-worker deterministic.
 *
 * @author Claude (KeY multithreading effort)
 */
public class NameAllocatorStressTest {

    private static final String[] BASES = { "x", "y", "skolem", "heap", "self" };

    @Test
    void concurrentMintingNeverCollides() throws Exception {
        final int workers = 8;
        final int namesPerWorker = 20_000;
        final ParallelNameAllocator allocator = new ParallelNameAllocator();

        final Set<String> all = ConcurrentHashMap.newKeySet();
        final List<Throwable> failures = new CopyOnWriteArrayList<>();
        final CountDownLatch start = new CountDownLatch(1);
        final CountDownLatch done = new CountDownLatch(workers);
        final List<Thread> threads = new ArrayList<>();

        for (int w = 0; w < workers; w++) {
            final int workerId = w;
            Thread t = new Thread(() -> {
                try {
                    start.await();
                    ParallelNameAllocator.runAsWorker(workerId, () -> {
                        for (int i = 0; i < namesPerWorker; i++) {
                            all.add(allocator.freshName(BASES[i % BASES.length]));
                        }
                    });
                } catch (Throwable th) {
                    failures.add(th);
                } finally {
                    done.countDown();
                }
            }, "stress-worker-" + w);
            threads.add(t);
            t.start();
        }

        start.countDown();
        assertTrue(done.await(60, TimeUnit.SECONDS), "stress workers did not finish in time");
        for (Thread t : threads) {
            t.join();
        }

        assertTrue(failures.isEmpty(), () -> "worker(s) threw: " + failures);
        // No duplicate names anywhere: the set holds exactly one entry per mint call.
        assertEquals(workers * namesPerWorker, all.size(),
            "duplicate names were produced under concurrent minting");
    }

    @Test
    void perWorkerSequenceIsDeterministic() {
        List<String> first = mintSequence(3);
        List<String> second = mintSequence(3);
        assertEquals(first, second,
            "the same worker minting the same sequence produced different names");
    }

    @Test
    void differentWorkersGetDisjointNames() {
        List<String> w0 = mintSequence(0);
        List<String> w1 = mintSequence(1);
        assertTrue(Collections.disjoint(w0, w1),
            () -> "worker 0 and worker 1 names overlap: " + w0 + " vs " + w1);
        // Worker 0 keeps the legacy untagged form; others are tagged.
        assertTrue(w0.stream().noneMatch(n -> n.contains("__t")),
            "worker 0 names must be untagged");
        assertTrue(w1.stream().allMatch(n -> n.contains("__t1")), "worker 1 names must carry __t1");
    }

    /** Mints a fixed sequence of names as the given worker on a fresh allocator. */
    private static List<String> mintSequence(int workerId) {
        ParallelNameAllocator allocator = new ParallelNameAllocator();
        List<String> names = new ArrayList<>();
        ParallelNameAllocator.runAsWorker(workerId, () -> {
            for (int i = 0; i < BASES.length * 3; i++) {
                names.add(allocator.freshName(BASES[i % BASES.length]));
            }
        });
        return names;
    }
}
