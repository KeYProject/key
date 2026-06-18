/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;

import de.uka.ilkd.key.prover.impl.GoalScheduler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Concurrency tests for {@link GoalScheduler}: each offered goal is claimed exactly once, the queue
 * deduplicates, and a pool of workers terminates exactly when the queue becomes quiescent &mdash;
 * including when processing a goal produces further goals (the proof-splitting case).
 *
 * @author Claude (KeY multithreading effort)
 */
public class GoalSchedulerTest {

    @Test
    void basicLifecycleAndQuiescence() {
        GoalScheduler<String> scheduler = new GoalScheduler<>();
        assertTrue(scheduler.isQuiescent());

        scheduler.offer("a");
        scheduler.offer("b");
        assertEquals(2, scheduler.availableCount());
        assertFalse(scheduler.isQuiescent());

        String first = scheduler.claimNext();
        assertEquals(1, scheduler.inFlightCount());
        assertFalse(scheduler.isQuiescent(), "in-flight work means not quiescent");

        String second = scheduler.claimNext(); // claim the other (order is an impl detail)
        assertNull(scheduler.claimNext(), "nothing left to claim");

        scheduler.complete(first);
        assertFalse(scheduler.isQuiescent(), "one goal still in flight");
        scheduler.complete(second);
        assertTrue(scheduler.isQuiescent(), "all goals completed");
    }

    @Test
    void deduplicatesByIdentity() {
        GoalScheduler<String> scheduler = new GoalScheduler<>();
        String g = "goal";
        scheduler.offer(g);
        scheduler.offer(g); // same identity, ignored
        assertEquals(1, scheduler.availableCount());

        String claimed = scheduler.claimNext();
        scheduler.offer(claimed); // in flight, must not be re-queued
        assertEquals(0, scheduler.availableCount());
    }

    @Test
    void concurrentWorkersClaimEachGoalExactlyOnceAndTerminate() throws Exception {
        final int workers = 6;
        final int initialGoals = 500;
        // Each goal, when processed, "splits" into children a bounded number of times, modelling
        // proof-tree growth. Total processed count is deterministic regardless of scheduling.
        final GoalScheduler<int[]> scheduler = new GoalScheduler<>();

        final Set<int[]> claimedOnce = ConcurrentHashMap.newKeySet();
        final List<int[]> claimedTwice = new CopyOnWriteArrayList<>();
        final AtomicInteger processed = new AtomicInteger();
        final List<Throwable> failures = new CopyOnWriteArrayList<>();

        for (int i = 0; i < initialGoals; i++) {
            scheduler.offer(new int[] { 3 }); // depth budget 3
        }

        final CountDownLatch ready = new CountDownLatch(workers);
        final CountDownLatch go = new CountDownLatch(1);
        List<Thread> threads = new ArrayList<>();
        for (int w = 0; w < workers; w++) {
            Thread t = new Thread(() -> {
                try {
                    ready.countDown();
                    go.await();
                    int[] goal;
                    while ((goal = scheduler.claimOrAwait()) != null) {
                        if (!claimedOnce.add(goal)) {
                            claimedTwice.add(goal);
                        }
                        processed.incrementAndGet();
                        // "Splitting": produce two children with a smaller depth budget.
                        if (goal[0] > 0) {
                            scheduler.offer(new int[] { goal[0] - 1 });
                            scheduler.offer(new int[] { goal[0] - 1 });
                        }
                        scheduler.complete(goal);
                    }
                } catch (Throwable th) {
                    failures.add(th);
                }
            }, "sched-worker-" + w);
            threads.add(t);
            t.start();
        }

        assertTrue(ready.await(5, TimeUnit.SECONDS));
        go.countDown();
        for (Thread t : threads) {
            t.join(60_000);
            assertFalse(t.isAlive(), "worker did not terminate at quiescence");
        }

        assertTrue(failures.isEmpty(), () -> "worker(s) threw: " + failures);
        assertTrue(claimedTwice.isEmpty(), "a goal was claimed by more than one worker");
        // Each initial goal spawns a full binary tree of depth 3: 1 + 2 + 4 + 8 = 15 nodes.
        assertEquals(initialGoals * 15, processed.get(), "unexpected number of processed goals");
        assertTrue(scheduler.isQuiescent(), "scheduler should be quiescent after all work");
    }

    /**
     * Models the prover's step exactly: a goal is completed AND its successors offered in one
     * atomic
     * {@link GoalScheduler#completeAndOffer} call. Starting from a single goal (so the depth-first
     * frontier stays small and the available queue is frequently empty mid-step), the whole tree
     * must still be processed. Were completion and offering not atomic, a worker could observe a
     * spurious quiescence in the gap and terminate the search early, processing fewer nodes.
     */
    @Test
    void completeAndOfferDoesNotTerminateSearchEarly() throws Exception {
        final int workers = 8;
        final int depth = 13; // full binary tree: 2^(depth+1) - 1 nodes
        final int expected = (1 << (depth + 1)) - 1;
        for (int rep = 0; rep < 5; rep++) {
            final GoalScheduler<int[]> scheduler = new GoalScheduler<>();
            final AtomicInteger processed = new AtomicInteger();
            final List<Throwable> failures = new CopyOnWriteArrayList<>();
            scheduler.offer(new int[] { depth }); // single root -> small frontier

            final CountDownLatch go = new CountDownLatch(1);
            List<Thread> threads = new ArrayList<>();
            for (int w = 0; w < workers; w++) {
                Thread t = new Thread(() -> {
                    try {
                        go.await();
                        int[] goal;
                        while ((goal = scheduler.claimOrAwait()) != null) {
                            processed.incrementAndGet();
                            List<int[]> kids = goal[0] > 0
                                    ? List.of(new int[] { goal[0] - 1 }, new int[] { goal[0] - 1 })
                                    : null;
                            scheduler.completeAndOffer(goal, kids);
                        }
                    } catch (Throwable th) {
                        failures.add(th);
                    }
                }, "sched-worker-" + w);
                threads.add(t);
                t.start();
            }
            go.countDown();
            for (Thread t : threads) {
                t.join(60_000);
                assertFalse(t.isAlive(), "worker did not terminate at quiescence");
            }
            assertTrue(failures.isEmpty(), () -> "worker(s) threw: " + failures);
            assertEquals(expected, processed.get(),
                "search terminated early (rep " + rep + ") -- completeAndOffer must be atomic");
            assertTrue(scheduler.isQuiescent());
        }
    }
}
