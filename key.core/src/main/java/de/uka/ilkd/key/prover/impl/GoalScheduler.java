/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.Set;

import org.jspecify.annotations.Nullable;

/**
 * Thread-safe work queue that hands out open goals to worker threads, the scheduling core of the
 * goal-level parallel prover (multithreading effort, branch {@code bubel/mt-goals}, Phase 3).
 *
 * <p>
 * This is a clean reimplementation of the 2018 {@code MultiCoreChooser} scheduling logic, decoupled
 * from the prover and using a <strong>single monitor</strong> instead of the original nested locks
 * &mdash; deliberately avoiding the lock-ordering fragility that made the earlier attempt
 * unmaintainable. It is parameterized over the goal type so it can be exercised in isolation.
 *
 * <p>
 * Lifecycle of an item:
 * <ul>
 * <li>{@link #offer}/{@link #offerAll} make a goal <em>available</em> (deduplicated by identity
 * against goals already available or in flight);
 * <li>{@link #claimNext} atomically moves an available goal to <em>in flight</em> and returns it;
 * <li>{@link #complete} marks an in-flight goal done (e.g. closed, or it produced new goals which
 * were offered);
 * <li>the queue is <em>quiescent</em> when nothing is available and nothing is in flight &mdash;
 * the signal that proof search has finished.
 * </ul>
 *
 * <p>
 * {@link #claimOrAwait} blocks while no goal is available but work is still in flight (more goals
 * may yet appear), and returns {@code null} only once the queue is quiescent &mdash; the natural
 * termination condition for a worker loop.
 *
 * @param <T> the goal type (the prover uses {@code GoalScheduler<Goal>}; tests use tokens)
 * @author Claude (KeY multithreading effort)
 */
public final class GoalScheduler<T> {

    private final Deque<T> available = new ArrayDeque<>();
    /**
     * Identity-set mirror of {@link #available}, so the duplicate check in {@link #offer} is O(1)
     * instead of a linear scan of the deque. This matters a lot: with a wide fan-out (and
     * especially
     * with few workers draining the queue) the available frontier grows large, and an O(n) scan per
     * offer made the whole run quadratic in the frontier width.
     */
    private final Set<T> availableSet = Collections.newSetFromMap(new IdentityHashMap<>());
    private final Set<T> inFlight = Collections.newSetFromMap(new IdentityHashMap<>());

    /**
     * Goals for which the strategy currently offers no rule application ({@link #stall}ed). They
     * are
     * <em>not</em> abandoned: KeY's rule-application cost is age-dependent, so a goal with no
     * applicable rule now may gain one once other goals advance the proof (and the shared state it
     * keys on). They are reactivated by {@link #claimOrAwait} once progress has been made,
     * mirroring
     * the single-threaded chooser, which retries goals across passes rather than dropping them.
     */
    private final Set<T> stalled = Collections.newSetFromMap(new IdentityHashMap<>());
    /** Whether a rule has been applied since the stalled goals were last reactivated. */
    private boolean progressMade;

    /** Makes {@code goal} available unless it is already available or in flight (by identity). */
    public synchronized void offer(T goal) {
        if (inFlight.contains(goal) || !availableSet.add(goal)) {
            return;
        }
        available.addLast(goal);
        notifyAll();
    }

    /** Offers each goal in {@code goals} (see {@link #offer}). */
    public synchronized void offerAll(Iterable<? extends T> goals) {
        for (T goal : goals) {
            offer(goal);
        }
    }

    /**
     * Atomically claims the next available goal, moving it to the in-flight set.
     *
     * <p>
     * Goals are handed out <em>last-in-first-out</em>: {@link #offer} appends and this polls from
     * the
     * same end, so each worker dives depth-first down a branch and a split's siblings sit on the
     * stack for other workers to pick up. This keeps the set of simultaneously-open goals small
     * (roughly the proof depth per worker) instead of the whole breadth of the proof tree, which a
     * FIFO order would hold open at once — a large, eviction-heavy working set that dominated
     * memory/GC (and ran several times slower) on wide, splitting proofs. Depth-first is also what
     * the single-threaded chooser does, keeping the two comparable.
     *
     * @return the claimed goal, or {@code null} if none is currently available
     */
    public synchronized @Nullable T claimNext() {
        T goal = available.pollLast();
        if (goal != null) {
            availableSet.remove(goal);
            inFlight.add(goal);
        }
        return goal;
    }

    /**
     * Claims the next goal to process, blocking while work may still appear.
     *
     * <p>
     * When no goal is immediately available it reactivates the {@link #stalled} goals &mdash; but
     * only once a rule has been applied since they stalled ({@link #progressMade}), so they are
     * retried in progress-gated batches rather than spun on. It returns {@code null} only when
     * nothing is available, nothing is in flight, and the stalled goals (if any) cannot be
     * reactivated because no progress was made &mdash; i.e. a full cycle yielded no rule for any
     * goal, the genuine "no more rules applicable to any goal" termination.
     *
     * @return the next goal to process, or {@code null} once the search is finished
     * @throws InterruptedException if the waiting thread is interrupted
     */
    public synchronized @Nullable T claimOrAwait() throws InterruptedException {
        while (true) {
            T goal = claimNext();
            if (goal != null) {
                return goal;
            }
            if (!stalled.isEmpty() && progressMade) {
                reactivateStalled();
                continue; // the reactivated goals are now available; claim one
            }
            if (inFlight.isEmpty()) {
                // nothing available, nothing reactivatable, nothing in flight: finished
                return null;
            }
            wait(); // an in-flight worker may yet apply a rule (progress) or stall its goal
        }
    }

    /**
     * Moves all stalled goals back to the available queue for another attempt (caller holds lock).
     */
    private void reactivateStalled() {
        for (T g : stalled) {
            if (availableSet.add(g)) {
                available.addLast(g);
            }
        }
        stalled.clear();
        progressMade = false;
    }

    /**
     * Records that the strategy currently offers no rule for {@code goal}: it is set aside
     * (stalled)
     * rather than abandoned, to be retried by {@link #claimOrAwait} once other goals make progress.
     *
     * @param goal the in-flight goal that yielded no rule application
     */
    public synchronized void stall(T goal) {
        inFlight.remove(goal);
        stalled.add(goal);
        notifyAll();
    }

    /**
     * Returns an in-flight goal to the available queue for immediate re-processing. Used when a
     * rule
     * application aborted but the goal still has further candidate rules to try: dropping it (via
     * {@link #complete}) would lose the goal and leave the proof open, while {@link #stall}ing
     * would
     * defer it to a progress-gated retry. Re-offering makes it available again right away,
     * mirroring
     * the single-threaded prover, which simply retries the goal after an aborted application.
     *
     * @param goal the in-flight goal whose rule application aborted
     */
    public synchronized void reoffer(T goal) {
        inFlight.remove(goal);
        if (availableSet.add(goal)) {
            available.addLast(goal);
        }
        notifyAll();
    }

    /** Marks an in-flight goal as done and wakes any threads waiting in {@link #claimOrAwait}. */
    public synchronized void complete(T goal) {
        inFlight.remove(goal);
        notifyAll();
    }

    /**
     * Atomically completes {@code goal} and offers its successors, as a single step under the
     * monitor.
     *
     * <p>
     * This must be atomic: if completing the goal and offering its successors were two separate
     * monitor sections, another worker could observe the queue between them &mdash; goal no longer
     * in flight, successors not yet available &mdash; and, finding nothing available and nothing in
     * flight, conclude (wrongly) that the search is quiescent and terminate, leaving the proof
     * open.
     * That gap is hit often under depth-first hand-out, where the frontier is small. Keeping the
     * two
     * together means a goal stays in flight until its successors are visible, so quiescence is only
     * ever observed when the search is genuinely finished.
     *
     * @param goal the just-processed goal to remove from the in-flight set
     * @param successors the open subgoals to make available (may be {@code null} or empty)
     */
    public synchronized void completeAndOffer(T goal, @Nullable Iterable<? extends T> successors) {
        inFlight.remove(goal);
        if (successors != null) {
            for (T s : successors) {
                if (!inFlight.contains(s) && availableSet.add(s)) {
                    available.addLast(s);
                }
            }
        }
        // A rule was applied, which may have made the stalled goals applicable again.
        progressMade = true;
        notifyAll();
    }

    /** Whether nothing is available, in flight, or stalled, i.e. proof search has finished. */
    public synchronized boolean isQuiescent() {
        return available.isEmpty() && inFlight.isEmpty() && stalled.isEmpty();
    }

    /** Number of goals currently available to claim. */
    public synchronized int availableCount() {
        return available.size();
    }

    /** Number of goals currently being processed. */
    public synchronized int inFlightCount() {
        return inFlight.size();
    }
}
