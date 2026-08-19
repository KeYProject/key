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

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.strategy.RuleApplicationManager;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;
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
 */
public class GoalSchedulerTest {

    private static final class TestGoal implements ProofGoal<TestGoal> {
        private final String name;
        private final int splitsLeft;
        private final boolean automatic;

        private TestGoal(String name, int splitsLeft, boolean automatic) {
            this.name = name;
            this.splitsLeft = splitsLeft;
            this.automatic = automatic;
        }

        @Override
        public String toString() {
            return name;
        }

        @Override
        public @Nullable ProofObject<TestGoal> proof() {
            return null;
        }

        @Override
        public @Nullable Sequent sequent() {
            return null;
        }

        @Override
        public @Nullable ImmutableList<TestGoal> apply(RuleApp ruleApp) {
            return null;
        }

        @Override
        public @Nullable RuleApplicationManager<TestGoal> getRuleAppManager() {
            return null;
        }

        @Override
        public long getTime() {
            return 0;
        }
    }

    /** An automatic goal that never splits. */
    private static TestGoal goal(String name) {
        return new TestGoal(name, 0, true);
    }

    /** An automatic goal that still splits {@code splitsLeft} times. */
    private static TestGoal splitting(int splitsLeft) {
        return new TestGoal("d" + splitsLeft, splitsLeft, true);
    }

    @Test
    void basicLifecycleAndQuiescence() {
        GoalScheduler<TestGoal> scheduler = new GoalScheduler<>();
        assertTrue(scheduler.isQuiescent());

        scheduler.offer(goal("a"));
        scheduler.offer(goal("b"));
        assertEquals(2, scheduler.availableCount());
        assertFalse(scheduler.isQuiescent());

        TestGoal first = scheduler.claimNext();
        assertEquals(1, scheduler.inFlightCount());
        assertFalse(scheduler.isQuiescent(), "in-flight work means not quiescent");

        TestGoal second = scheduler.claimNext(); // claim the other (order is an impl detail)
        assertNull(scheduler.claimNext(), "nothing left to claim");

        scheduler.complete(first);
        assertFalse(scheduler.isQuiescent(), "one goal still in flight");
        scheduler.complete(second);
        assertTrue(scheduler.isQuiescent(), "all goals completed");
    }

    @Test
    void deduplicatesByIdentity() {
        GoalScheduler<TestGoal> scheduler = new GoalScheduler<>();
        TestGoal g = goal("goal");
        scheduler.offer(g);
        scheduler.offer(g); // same identity, ignored
        assertEquals(1, scheduler.availableCount());

        TestGoal claimed = scheduler.claimNext();
        scheduler.offer(claimed); // in flight, must not be re-queued
        assertEquals(0, scheduler.availableCount());
    }

    @Test
    void concurrentWorkersClaimEachGoalExactlyOnceAndTerminate() throws Exception {
        final int workers = 6;
        final int initialGoals = 500;
        // Each goal, when processed, "splits" into children a bounded number of times, modelling
        // proof-tree growth. Total processed count is deterministic regardless of scheduling.
        final GoalScheduler<TestGoal> scheduler = new GoalScheduler<>();

        final Set<TestGoal> claimedOnce = ConcurrentHashMap.newKeySet();
        final List<TestGoal> claimedTwice = new CopyOnWriteArrayList<>();
        final AtomicInteger processed = new AtomicInteger();
        final List<Throwable> failures = new CopyOnWriteArrayList<>();

        for (int i = 0; i < initialGoals; i++) {
            scheduler.offer(splitting(3)); // depth budget 3
        }

        final CountDownLatch ready = new CountDownLatch(workers);
        final CountDownLatch go = new CountDownLatch(1);
        List<Thread> threads = new ArrayList<>();
        for (int w = 0; w < workers; w++) {
            Thread t = new Thread(() -> {
                try {
                    ready.countDown();
                    go.await();
                    TestGoal goal;
                    while ((goal = scheduler.claimOrAwait()) != null) {
                        if (!claimedOnce.add(goal)) {
                            claimedTwice.add(goal);
                        }
                        processed.incrementAndGet();
                        // "Splitting": produce two children with a smaller depth budget.
                        if (goal.splitsLeft > 0) {
                            scheduler.offer(splitting(goal.splitsLeft - 1));
                            scheduler.offer(splitting(goal.splitsLeft - 1));
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
            final GoalScheduler<TestGoal> scheduler = new GoalScheduler<>();
            final AtomicInteger processed = new AtomicInteger();
            final List<Throwable> failures = new CopyOnWriteArrayList<>();
            scheduler.offer(splitting(depth)); // single root -> small frontier

            final CountDownLatch go = new CountDownLatch(1);
            List<Thread> threads = new ArrayList<>();
            for (int w = 0; w < workers; w++) {
                Thread t = new Thread(() -> {
                    try {
                        go.await();
                        TestGoal goal;
                        while ((goal = scheduler.claimOrAwait()) != null) {
                            processed.incrementAndGet();
                            List<TestGoal> kids = goal.splitsLeft > 0
                                    ? List.of(splitting(goal.splitsLeft - 1),
                                        splitting(goal.splitsLeft - 1))
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

    /**
     * A stalled goal that is offered again must not become schedulable twice (C1). {@link
     * GoalScheduler#offer} now excludes stalled goals, so re-offering one is a no-op and it is
     * handed out exactly once when the progress-driven reactivation brings it back.
     */
    @Test
    void offeringAStalledGoalDoesNotDoubleScheduleIt() throws Exception {
        GoalScheduler<TestGoal> scheduler = new GoalScheduler<>();
        TestGoal g = goal("g");
        TestGoal driver = goal("driver"); // a second goal whose completion signals progress
        // offer driver first so g is on top of the LIFO stack and is claimed first
        scheduler.offer(driver);
        scheduler.offer(g);

        assertEquals(g, scheduler.claimNext());
        scheduler.stall(g); // g is stalled; driver stays available
        assertEquals(1, scheduler.availableCount(), "only driver remains available; g is stalled");

        scheduler.offer(g); // re-offer the still-stalled goal: must be ignored
        assertEquals(1, scheduler.availableCount(), "re-offering a stalled goal must not queue it");

        // Make progress on the driver, which reactivates the stalled set exactly once.
        assertEquals(driver, scheduler.claimNext());
        scheduler.completeAndOffer(driver, null);

        assertEquals(g, scheduler.claimOrAwait(), "g reactivated and claimed once");
        scheduler.completeAndOffer(g, null);
        assertNull(scheduler.claimNext(), "g must not be claimable a second time");
        assertTrue(scheduler.isQuiescent());
    }

    /**
     * Reactivation of stalled goals happens only after progress and in deterministic insertion
     * order (C2): the stalled set is insertion-ordered, so reactivation appends the goals in the
     * order they stalled and the LIFO hand-out then claims them in reverse. This order must not
     * depend on JVM identity-hash layout.
     */
    @Test
    void stalledGoalsReactivateOnlyAfterProgressInDeterministicOrder() throws Exception {
        GoalScheduler<TestGoal> scheduler = new GoalScheduler<>();
        TestGoal driver = goal("driver");
        TestGoal g1 = goal("g1");
        TestGoal g2 = goal("g2");
        TestGoal g3 = goal("g3");
        scheduler.offer(driver);

        // Stall g1, g2, g3 in that order (each is the LIFO top when claimed).
        for (TestGoal g : new TestGoal[] { g1, g2, g3 }) {
            scheduler.offer(g);
            assertEquals(g, scheduler.claimNext());
            scheduler.stall(g);
        }
        assertFalse(scheduler.isQuiescent(), "stalled goals keep the queue busy until retried");

        // Progress: completing the driver flips progressMade and lets the stalled set reactivate.
        assertEquals(driver, scheduler.claimNext());
        scheduler.completeAndOffer(driver, null);

        // Reactivation appends g1,g2,g3 (insertion order); LIFO hand-out then claims g3,g2,g1.
        List<TestGoal> claimOrder = new ArrayList<>();
        TestGoal claimed;
        while ((claimed = scheduler.claimOrAwait()) != null) {
            claimOrder.add(claimed);
            scheduler.completeAndOffer(claimed, null);
        }
        assertEquals(List.of(g3, g2, g1), claimOrder, "deterministic reactivation/claim order");
        assertTrue(scheduler.isQuiescent());
    }

    /**
     * {@link GoalScheduler#reoffer} returns an in-flight goal to the queue so it is immediately
     * claimable again &mdash; without waiting for progress (unlike {@link GoalScheduler#stall}).
     */
    @Test
    void reofferMakesGoalImmediatelyClaimable() {
        GoalScheduler<TestGoal> scheduler = new GoalScheduler<>();
        TestGoal g = goal("g");
        scheduler.offer(g);
        assertEquals(g, scheduler.claimNext());
        assertEquals(0, scheduler.availableCount());
        assertEquals(1, scheduler.inFlightCount());

        scheduler.reoffer(g); // aborted rule app: retry immediately, no progress gate
        assertEquals(1, scheduler.availableCount(), "reoffered goal is available at once");
        assertEquals(0, scheduler.inFlightCount());
        assertFalse(scheduler.isQuiescent());

        assertEquals(g, scheduler.claimNext(), "reoffered goal is claimable again");
        scheduler.complete(g);
        assertTrue(scheduler.isQuiescent());
    }

    /**
     * {@link GoalScheduler#offerAll} makes every goal in the batch available (deduplicating by
     * identity), and is a no-op for goals already available or in flight.
     */
    @Test
    void offerAllMakesEachGoalAvailableAndDeduplicates() {
        GoalScheduler<TestGoal> scheduler = new GoalScheduler<>();
        TestGoal a = goal("a");
        TestGoal b = goal("b");
        scheduler.offerAll(List.of(a, b, a)); // duplicate a collapses
        assertEquals(2, scheduler.availableCount());

        TestGoal claimed = scheduler.claimNext();
        scheduler.offerAll(List.of(claimed, goal("c"))); // in-flight claimed ignored, c added
        assertEquals(2, scheduler.availableCount(), "in-flight goal not re-queued; new goal added");
    }

    /**
     * When the search finishes with a goal left stalled and no progress to reactivate it, {@link
     * GoalScheduler#claimOrAwait} returns {@code null} (worker termination) while {@link
     * GoalScheduler#isQuiescent} deliberately stays {@code false} -- it reports strict drain, a
     * stronger property than "search finished" (C3). The two are documented to differ in exactly
     * this terminal state.
     */
    @Test
    void searchTerminatesButIsQuiescentStaysFalseWhenGoalsEndStalled() throws Exception {
        GoalScheduler<TestGoal> scheduler = new GoalScheduler<>();
        TestGoal g = goal("g");
        scheduler.offer(g);
        assertEquals(g, scheduler.claimNext());
        scheduler.stall(g); // no progress was made this pass

        // A whole cycle produced no rule for any goal: the search is genuinely finished.
        assertNull(scheduler.claimOrAwait(), "no progress + all goals stalled -> finished");
        assertFalse(scheduler.isQuiescent(),
            "isQuiescent stays false while a stalled goal is still held, though the search ended");
    }
}
