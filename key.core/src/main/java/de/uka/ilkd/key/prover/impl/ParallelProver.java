/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.TaskStartedInfo;
import org.key_project.prover.engine.impl.ApplyStrategyInfo;
import org.key_project.prover.engine.impl.DefaultProver;
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Goal-level parallel prover. Enabled via the general settings (the prover-mode preference, also
 * toggled from the status-line indicator); the {@code -Dkey.prover.parallel} system property,
 * when set, transiently overrides that preference in either direction (see {@link #isEnabled()}).
 *
 * <p>
 * A fixed pool of worker threads (count from the settings, clamped to the available processors;
 * see {@link #effectiveWorkerCount()}): a {@link GoalScheduler} hands out open goals to the
 * workers; each worker applies rules to its goal and offers the resulting subgoals back to the
 * scheduler. The run finishes when the scheduler becomes quiescent (no goal available and none in
 * flight) or a stop condition fires. Non-proving listeners are suspended for the whole run.
 * Fresh names need no per-worker treatment: minting searches the goal-local
 * namespaces, so a name is a pure function of the branch state, identical no matter which worker
 * processes the goal (#3851).
 *
 * <p>
 * <b>Concurrency model.</b> The per-goal rule step splits into a concurrent part and a serialized
 * part. Rule selection (matching + cost) and the rule executor ({@link Goal#computeRuleApp}) run in
 * parallel across workers; only the proof-tree commit ({@link Goal#commitRuleApp}) runs under a
 * single {@code commitLock}, so tree mutation stays mutually exclusive. The scheduler hand-off and
 * the run counters (which are atomic) stay outside the lock. Running the executor outside the lock
 * is what makes this faster than single-threaded; it is sound because the shared structures the
 * executor reaches through the {@link org.key_project.logic.Services} were made thread-safe by the
 * shared-state audit (lazy type caches, the specification repository, operator/parametric-function
 * interning, built-in-rule instantiation caches, NodeInfo/RuleJustificationInfo, the
 * OneStepSimplifier, the shared taclet-index cache), and fresh-name minting searches only the
 * goal-local namespaces of the owning worker's goal (branch-state-derived, #3851), never writing
 * to the shared namespace. The equivalence gate ({@code ProofEquivalenceTest}) and the real-proof
 * gate guard the whole design.
 *
 * <p>
 * <b>Limitation.</b> A custom goal chooser configured for a proof or profile applies only to the
 * single-threaded prover: the parallel engine schedules goals through its {@link GoalScheduler}
 * and does not consult the {@link GoalChooser} it is constructed with (the constructor keeps the
 * parameter for API symmetry with {@code ApplyStrategy}).
 *
 * @author Claude (KeY multithreading effort)
 */
public final class ParallelProver extends DefaultProver<Proof, Goal> {

    private static final Logger LOGGER = LoggerFactory.getLogger(ParallelProver.class);

    /** When {@code true}, the auto-prover selection point builds a {@link ParallelProver}. */
    public static final String PARALLEL_PROPERTY = "key.prover.parallel";
    /** Number of worker threads. */
    public static final String THREADS_PROPERTY = "key.prover.parallel.threads";

    /** Names worker thread pools uniquely for debugging/profiling. */
    private static final AtomicInteger POOL_COUNTER = new AtomicInteger();

    /** Number of parallel runs with more than one worker currently in progress (global). */
    private static final AtomicInteger ACTIVE_MULTI_WORKER_RUNS = new AtomicInteger();

    /**
     * Whether a goal-level parallel run with more than one worker is currently in progress. Rules
     * that are not yet safe under concurrent goal processing consult this to disable themselves for
     * the duration; single-threaded proving (and the old main-thread prover) is unaffected.
     *
     * @return {@code true} iff at least one multi-worker parallel run is active
     * @see de.uka.ilkd.key.rule.merge.MergeRule
     */
    public static boolean isMultiThreadedRunActive() {
        return ACTIVE_MULTI_WORKER_RUNS.get() > 0;
    }

    /** A closeable scope whose {@link #close()} does not throw a checked exception. */
    public interface RunScope extends AutoCloseable {
        @Override
        void close();
    }

    /**
     * Marks a multi-worker run as active until the returned handle is closed. Exposed for the
     * prover's own run scope and for tests of the rules that gate on
     * {@link #isMultiThreadedRunActive()}.
     *
     * @return a {@link RunScope} that clears the marker on close
     */
    public static RunScope enterMultiThreadedRun() {
        ACTIVE_MULTI_WORKER_RUNS.incrementAndGet();
        return ACTIVE_MULTI_WORKER_RUNS::decrementAndGet;
    }

    private final int workerCount;

    /**
     * Set once a stop condition fires. {@link #requestStop} flips this with a compare-and-set so
     * the
     * first caller wins atomically -- the {@link #stopMessage}/{@link #nonCloseableGoal} pair is
     * then
     * written only by that winner, never interleaved between two concurrent stop requests.
     */
    private final AtomicBoolean stopRequested = new AtomicBoolean();
    /** Set by {@link #requestStop} under the winning CAS; read once after the run. */
    private volatile @Nullable String stopMessage;

    /**
     * The first uncaught error from any worker, recorded before that worker rethrows. Read after
     * the
     * run so the reported error is deterministic (first-recorded), not whichever {@link Future} the
     * join loop happens to observe first.
     */
    private final AtomicReference<@Nullable Throwable> firstError = new AtomicReference<>();

    /**
     * How long {@link #awaitWorkerTermination} waits for the workers to wind down after a stop. The
     * stop is cooperative (workers leave their claim loop after the current step), so this is only
     * a
     * safety cap to avoid blocking the caller forever should a worker get genuinely stuck.
     */
    private static final long WORKER_SHUTDOWN_TIMEOUT_SECONDS = 60;
    private volatile @Nullable Goal nonCloseableGoal;

    /**
     * Applied-rule and closed-goal counters maintained lock-free during the run, so the per-step
     * bookkeeping does not need the commit lock. They are mirrored into the inherited
     * {@code countApplied}/{@code closedGoals} fields when the run finishes (for the result).
     */
    private final AtomicInteger appliedSteps = new AtomicInteger();
    private final AtomicInteger closedCount = new AtomicInteger();

    /**
     * @param goalChooser kept for API symmetry with {@link ApplyStrategy}; the parallel engine uses
     *        a {@link GoalScheduler} for goal selection rather than this chooser
     */
    public ParallelProver(GoalChooser<Proof, Goal> goalChooser) {
        this.goalChooser = goalChooser;
        this.workerCount = resolveWorkerCount();
    }

    /**
     * Whether the parallel prover is selected. The system property {@link #PARALLEL_PROPERTY}, when
     * set, overrides the user setting (so tests, benchmarks and the CLI can pin a mode regardless
     * of
     * the persisted preference); otherwise the {@link GeneralSettings#isParallelProverEnabled()
     * setting} decides.
     */
    public static boolean isEnabled() {
        String property = System.getProperty(PARALLEL_PROPERTY);
        if (property != null) {
            return Boolean.parseBoolean(property);
        }
        return generalSettings().isParallelProverEnabled();
    }

    /**
     * The number of workers a run started now would use. As with {@link #isEnabled()}, the
     * {@link #THREADS_PROPERTY} overrides the setting (and is honoured exactly, allowing the
     * over-subscription the stress tests rely on); the setting-derived count is clamped to the
     * available processors. Exposed so tests can assert that a "multi-worker" run really is
     * multi-worker rather than having silently degraded to a single worker.
     *
     * @return the effective worker count for the current settings / system properties
     */
    public static int effectiveWorkerCount() {
        return resolveWorkerCount();
    }

    private static int resolveWorkerCount() {
        String property = System.getProperty(THREADS_PROPERTY);
        if (property != null) {
            try {
                return Math.max(1, Integer.parseInt(property));
            } catch (NumberFormatException e) {
                return 1;
            }
        }
        int configured = generalSettings().getParallelProverThreadCount();
        return Math.max(1, Math.min(configured, Runtime.getRuntime().availableProcessors()));
    }

    private static GeneralSettings generalSettings() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
    }

    /** The number of worker threads this prover uses. */
    public int getWorkerCount() {
        return workerCount;
    }

    @Override
    protected final @Nullable RuleApp updateBuiltInRuleIndex(Goal goal, @Nullable RuleApp app) {
        // Hack mirrored from ApplyStrategy: built-in rules may become applicable without the
        // BuiltInRuleAppIndex noticing.
        if (app == null) {
            goal.ruleAppIndex().scanBuiltInRules(goal);
            app = goal.getRuleAppManager().next();
        }
        return app;
    }

    @Override
    public ApplyStrategyInfo<Proof, Goal> start(Proof proof, Goal goal) {
        return start(proof, ImmutableList.<Goal>nil().prepend(goal));
    }

    @Override
    public ApplyStrategyInfo<Proof, Goal> start(Proof proof, ImmutableList<Goal> goals) {
        ProofSettings settings = proof.getSettings();
        return start(proof, goals, settings.getStrategySettings());
    }

    @Override
    public ApplyStrategyInfo<Proof, Goal> start(Proof proof, ImmutableList<Goal> goals,
            Object strategySettings) {
        final StrategySettings stratSet = (StrategySettings) strategySettings;
        int maxSteps = stratSet.getMaxSteps();
        long timeout = stratSet.getTimeout();
        boolean stopAtFirstNonCloseableGoal = proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties().getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
        return start(proof, goals, maxSteps, timeout, stopAtFirstNonCloseableGoal);
    }

    // synchronized on 'this' for the whole run, mirroring DefaultProver.doWork: the GUI's
    // AutoModeWorker.done() waits for the run to finish via synchronized(applyStrategy) before it
    // clears the prover, so without this the Stop button could null the proof and read a
    // not-yet-set
    // result while workers were still winding down. The workers never take this monitor (progress
    // is
    // no longer fired per step, see processStep), so holding it for the run cannot deadlock them.
    @Override
    public synchronized ApplyStrategyInfo<Proof, Goal> start(Proof proof, ImmutableList<Goal> goals,
            int maxSteps,
            long timeout, boolean stopAtFirstNonCloseableGoal) {
        assert proof != null;
        this.proof = proof;
        this.stopAtFirstNonClosableGoal = stopAtFirstNonCloseableGoal;
        this.stopCondition =
            proof.getSettings().getStrategySettings().getApplyStrategyStopCondition();
        this.maxApplications = stopCondition.getMaximalWork(maxSteps, timeout);
        this.timeout = timeout;
        this.countApplied = 0;
        this.closedGoals = 0;
        this.appliedSteps.set(0);
        this.closedCount.set(0);
        this.cancelled = false;
        this.stopRequested.set(false);
        this.stopMessage = null;
        this.nonCloseableGoal = null;
        this.firstError.set(null);

        // size 0 -> the status line shows an indeterminate ("busy") bar: the parallel prover does
        // not report a meaningful per-step progress value (workers commit concurrently), so a
        // determinate bar would either sit at zero or need thread-unsafe cross-worker counting.
        fireTaskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Strategy,
            PROCESSING_STRATEGY, 0));

        ApplyStrategyInfo<Proof, Goal> result = runParallel(goals);

        proof.addAutoModeTime(result.getTime());
        fireTaskFinished(new DefaultTaskFinishedInfo(this, result, proof, result.getTime(),
            result.getNumberOfAppliedRuleApps(), result.getNumberOfClosedGoals()));
        return result;
    }

    private ApplyStrategyInfo<Proof, Goal> runParallel(ImmutableList<Goal> goals) {
        final long startTime = System.currentTimeMillis();
        final GoalScheduler<Goal> scheduler = new GoalScheduler<>();
        scheduler.offerAll(goals);
        final Object commitLock = new Object();

        // Enter the multi-worker run scope (MT-active marker + sealed Java types) with guaranteed
        // teardown: the pool is created *inside* this scope so that a failure while entering it
        // (e.g.
        // sealing) can never leak the marker or an unshut pool.
        final RunScope mtScope = enterMultiWorkerRunScope();
        try {
            final int poolId = POOL_COUNTER.incrementAndGet();
            final ExecutorService pool = Executors.newFixedThreadPool(workerCount, r -> {
                Thread t = new Thread(r, "key-prover-" + poolId + "-worker");
                t.setDaemon(true);
                return t;
            });
            try (var ignored = proof.suspendNonEssentialListeners()) {
                List<Future<?>> futures = new ArrayList<>(workerCount);
                try {
                    for (int w = 0; w < workerCount; w++) {
                        futures.add(
                            pool.submit(() -> workerLoop(scheduler, commitLock, startTime)));
                    }
                    for (Future<?> f : futures) {
                        f.get();
                    }
                } catch (ExecutionException e) {
                    // A worker terminated exceptionally. workerLoop recorded the first such error
                    // in
                    // firstError (and asked the others to stop) before rethrowing, so the reported
                    // error below is deterministic regardless of which future we observe here.
                    LOGGER.warn("parallel prover: a worker terminated exceptionally", e.getCause());
                } catch (InterruptedException e) {
                    cancelled = true;
                } finally {
                    // Stop the workers and WAIT for them to actually finish while the non-essential
                    // (GUI) proof-tree listeners are STILL suspended by the enclosing
                    // try-with-resources -- the inner finally runs before the resource is closed.
                    // If
                    // we returned (and let the listeners be re-attached) while a worker was still
                    // mid-step, that worker would deliver a proofExpanded event into the live Swing
                    // proof-tree model off the EDT and deadlock against it: the EDT holds the AWT
                    // tree lock and wants the GUIProofTreeModel monitor, while the worker holds
                    // that
                    // monitor and wants the AWT tree lock. stopRequested makes the workers leave
                    // their claim loop; shutdownNow unblocks any parked in the scheduler.
                    stopRequested.set(true);
                    pool.shutdownNow();
                    awaitWorkerTermination(pool);
                }
            }
        } finally {
            mtScope.close();
        }

        // Publish the lock-free counters into the inherited fields for the result.
        countApplied = appliedSteps.get();
        closedGoals = closedCount.get();

        final Throwable error = firstError.get();
        long time = System.currentTimeMillis() - startTime;
        final String message;
        if (error != null) {
            message = "Error.";
        } else if (cancelled) {
            message = "Interrupted.";
        } else if (stopMessage != null) {
            message = stopMessage;
        } else {
            message = "No more rules automatically applicable to any goal.";
        }
        return new ApplyStrategyInfo<>(message, proof, error, nonCloseableGoal, time, countApplied,
            closedGoals);
    }

    /**
     * Enters the multi-worker run scope: while more than one worker runs, advertise that a
     * multi-threaded run is active (so rules not yet safe under concurrency, e.g. MergeRule,
     * disable
     * themselves) and seal the Java type model (no new type may be registered while workers prove
     * concurrently; types are pre-registered at load time, so a stray lazy registration now fails
     * fast instead of racing the shared model). The returned scope reverses both on close. If
     * sealing throws, the active-run marker is released before propagating, so it never leaks.
     *
     * @return a scope reversing the markers on close; a no-op scope for a single-worker run
     */
    private RunScope enterMultiWorkerRunScope() {
        if (workerCount <= 1) {
            return () -> {
            };
        }
        final RunScope marker = enterMultiThreadedRun();
        try {
            final JavaInfo javaInfo = proof.getServices().getJavaInfo();
            // Materialise the default execution context on this proof's (fresh) JavaInfo before
            // sealing, so the matcher reads it instead of registering it during the run.
            javaInfo.getDefaultExecutionContext();
            javaInfo.sealTypeRegistration();
            return () -> {
                javaInfo.unsealTypeRegistration();
                marker.close();
            };
        } catch (Throwable t) {
            marker.close();
            throw t;
        }
    }

    /**
     * Waits for the worker pool to terminate after {@link ExecutorService#shutdownNow()}. The wait
     * runs with the calling thread's interrupt status cleared (the run is often stopped by
     * interrupting this very thread, which would otherwise make {@code awaitTermination} return
     * immediately and defeat the purpose) and restores the status afterwards; further interrupts
     * arriving mid-wait are likewise absorbed and the wait continues on the remaining budget. The
     * generous timeout accommodates a worker that is mid-step (e.g. a large taclet match) when
     * asked to stop; the stop is cooperative, so it returns as soon as the last worker leaves its
     * step.
     */
    private void awaitWorkerTermination(ExecutorService pool) {
        boolean wasInterrupted = Thread.interrupted();
        final long deadlineNanos =
            System.nanoTime() + TimeUnit.SECONDS.toNanos(WORKER_SHUTDOWN_TIMEOUT_SECONDS);
        boolean terminated = pool.isTerminated();
        while (!terminated) {
            final long remainingNanos = deadlineNanos - System.nanoTime();
            if (remainingNanos <= 0) {
                break;
            }
            try {
                terminated = pool.awaitTermination(remainingNanos, TimeUnit.NANOSECONDS);
            } catch (InterruptedException e) {
                // A further stop interrupt arrived mid-wait. This method exists precisely so the
                // run does not return while a worker may still be mutating the proof (see the
                // caller's deadlock note), so remember the interrupt and wait out the remaining
                // budget instead of bailing early.
                wasInterrupted = true;
            }
        }
        if (!terminated) {
            // A worker did not leave its step within the (generous) cap: it is genuinely stuck,
            // which Java cannot force-terminate. Surface it as a run error so the caller does not
            // treat the returned proof as complete, rather than silently returning while a
            // worker may still be mutating it.
            LOGGER.error("parallel prover workers did not stop within {}s of a stop request; "
                + "the returned proof may be incomplete", WORKER_SHUTDOWN_TIMEOUT_SECONDS);
            firstError.compareAndSet(null,
                new IllegalStateException("parallel prover workers did not terminate within "
                    + WORKER_SHUTDOWN_TIMEOUT_SECONDS + "s of a stop request"));
        }
        if (wasInterrupted) {
            Thread.currentThread().interrupt();
        }
    }

    /** A single worker: claim goals and process them until the queue is quiescent or stopped. */
    private void workerLoop(GoalScheduler<Goal> scheduler, Object commitLock,
            long startTime) {
        // The rule executor's fresh-name proposals (made in the lock-free compute phase) go through
        // Services' per-thread name recorder, so this worker records into its own recorder with no
        // race on a shared one -- see Services#getNameRecorder. No explicit binding is needed: the
        // recorder is created lazily per thread and this worker pool is created fresh per run.
        try {
            Goal goal;
            while (!stopRequested.get() && (goal = scheduler.claimOrAwait()) != null) {
                if (proof.isErroneous()) {
                    // An essential proof listener failed on some worker: wind all workers down
                    // through the regular stop path (the claimed goal is returned below by the
                    // loop exit; parked workers wake through the scheduler as with any stop).
                    // Checking a volatile flag once per rule application is free next to the
                    // step itself; no push notification into the workers is needed.
                    requestStop("Proof search stopped: an essential proof listener failed.", null);
                    scheduler.reoffer(goal);
                    break;
                }
                processStep(goal, scheduler, commitLock, startTime);
            }
        } catch (InterruptedException e) {
            // Workers are only ever interrupted by the wind-down's shutdownNow, which runs on
            // normal completion, user stop and error stop alike -- so this carries no "user
            // cancelled" information (a genuine cancel is recorded by start()'s own
            // InterruptedException handler). Setting cancelled here would misreport an
            // error-stopped run as user-interrupted to macro/script drivers.
            Thread.currentThread().interrupt();
        } catch (Throwable t) {
            // A worker died unexpectedly (e.g. a bug reached during a rule step). Record the first
            // such error and ask all workers to stop, so the proof is not driven further under
            // possibly corrupted state (the survivors see stopRequested and leave their loop). The
            // reoffer/complete bookkeeping for the claimed goal is handled by processStep's
            // finally;
            // rethrow so the failure still surfaces via this worker's Future.
            firstError.compareAndSet(null, t);
            requestStop("Error.", null);
            throw t;
        }
    }

    /**
     * Performs one rule step on {@code goal}: select a rule, apply it, and offer the resulting open
     * subgoals back to the scheduler.
     *
     * <p>
     * <b>Rule selection runs outside the commit lock</b> — this is where the time goes (taclet
     * matching + strategy cost), and it is safe to run concurrently: the goal is owned exclusively
     * by this worker (the scheduler hands each goal to one worker), the shared proof namespace is
     * immutable during the run (see {@code Goal#adaptNamespacesNewGoals}), fresh names derive
     * from the goal-local branch state alone (#3851), and the strategy caches are thread-safe
     * (shared exact-LRU). The commit lock wraps <em>only</em> {@code Goal#commitRuleApp} — the
     * proof-tree mutation, the one genuinely shared non-thread-safe step. The scheduler hand-off,
     * counters, progress and stop check run outside it (the scheduler has its own monitor and the
     * counters are atomic), so workers serialize on nothing but the tree mutation itself.
     */
    private void processStep(Goal goal, GoalScheduler<Goal> scheduler, Object commitLock,
            long startTime) {
        // Whether the goal was handed back to the scheduler in this step (stalled, or completed and
        // its successors offered). If it leaves the step any other way -- stop requested, or the
        // rule aborted -- the finally below drops it from the in-flight set. Exactly one of these
        // happens per goal, which is what keeps the scheduler's accounting (and termination) sound.
        boolean handled = false;
        try {
            if (stopRequested.get()) {
                return;
            }
            // --- selection: concurrent across workers, no commit lock held ---
            // countApplied is read without the lock; a slightly stale value only affects the
            // step-limit heuristic (at worst a tiny overshoot), never soundness.
            if (!stopCondition.isGoalAllowed(goal, maxApplications, timeout, startTime,
                appliedSteps.get())) {
                requestStop(stopCondition.getGoalNotAllowedMessage(goal, maxApplications,
                    timeout, startTime, appliedSteps.get()), null);
                return;
            }

            RuleApp app = goal.getRuleAppManager().next();
            app = updateBuiltInRuleIndex(goal, app);

            if (app == null) {
                // The strategy currently offers no rule for this goal. With STOPMODE_NONCLOSE that
                // is a hard stop; otherwise the goal is *stalled*, not dropped: KeY's cost is
                // age-dependent, so the goal may gain an applicable rule once other goals advance
                // the
                // proof. The scheduler retries stalled goals after progress and only abandons them
                // once a whole cycle makes none -- mirroring the single-threaded chooser, which
                // retries goals across passes instead of discarding them on the first empty pass.
                if (stopAtFirstNonClosableGoal) {
                    requestStop("Could not close goal.", goal);
                } else {
                    scheduler.stall(goal);
                    handled = true;
                }
                return;
            }

            // --- apply: the executor runs concurrently; only the tree commit is serialized ---
            // computeRuleApp (rule execution / term construction) is safe to run in parallel: the
            // shared structures it reaches through the Services were made thread-safe by the
            // shared-state audit. Only commitRuleApp -- the proof-tree mutation -- needs the commit
            // lock; the scheduler hand-off, the atomic counters and the stop check stay outside it.
            Goal.PendingRuleApp pending = goal.computeRuleApp(app);
            if (pending == null) {
                // The rule application aborted. The candidate rule was already removed from the
                // goal's queue by next() above, so re-offer the goal to retry with its next
                // candidate instead of dropping it -- dropping loses the goal and can leave the
                // proof open. This mirrors the single-threaded prover, which retries the goal after
                // an aborted application rather than discarding it.
                scheduler.reoffer(goal);
                handled = true;
                return;
            }

            final ImmutableList<Goal> goalList;
            synchronized (commitLock) {
                goalList = goal.commitRuleApp(pending);
            }

            final int applied = appliedSteps.incrementAndGet();
            // No per-step progress event: the status line shows an indeterminate bar for the whole
            // parallel run (see start()), and firing taskProgress concurrently from every worker
            // would drive listeners written for the single-threaded prover (e.g. AutoSaver, which
            // serialises the proof) off the worker threads. The final counts reach listeners
            // through
            // taskFinished. Autosave-during-run is therefore inactive under the parallel prover.

            // Partition the successors into closed (just counted) and open (to be rescheduled).
            int closedNow = 0;
            List<Goal> open = null;
            if (goalList != null) {
                closedNow = goalList.isEmpty() ? 1 : 0;
                for (Goal g : goalList) {
                    if (g.node().isClosed()) {
                        closedNow++;
                    } else {
                        if (open == null) {
                            open = new ArrayList<>(2);
                        }
                        open.add(g);
                    }
                }
            }
            // Complete this goal and offer its open successors as one atomic scheduler step (see
            // GoalScheduler#completeAndOffer): a separate complete-then-offer would let another
            // worker observe the queue momentarily empty in between and stop the search early.
            scheduler.completeAndOffer(goal, open);
            handled = true;
            if (closedNow > 0) {
                closedCount.addAndGet(closedNow);
            }

            if (stopCondition.shouldStop(maxApplications, timeout, startTime, applied, null)) {
                requestStop(stopCondition.getStopMessage(maxApplications, timeout, startTime,
                    applied, null), null);
            }
        } finally {
            // Backstop for goals that left the step early (stop requested, or rule aborted):
            // release
            // them from the in-flight set so the scheduler can still reach quiescence. The handled
            // paths above already accounted for the goal, so this runs only when none of them did.
            if (!handled) {
                scheduler.complete(goal);
            }
        }
    }

    /**
     * Records the first stop reason and signals all workers to finish. The compare-and-set makes
     * the
     * "first caller wins" atomic: only the winner writes the {@link #stopMessage}/
     * {@link #nonCloseableGoal} pair (read after the run), so two concurrent stop requests can
     * never
     * mix one's message with the other's goal.
     */
    private void requestStop(String message, @Nullable Goal goal) {
        if (stopRequested.compareAndSet(false, true)) {
            stopMessage = message;
            nonCloseableGoal = goal;
        }
    }

    @Override
    public synchronized void clear() {
        proof = null;
        if (goalChooser != null) {
            goalChooser.init(null, ImmutableList.nil());
        }
    }

    @Override
    public boolean hasBeenInterrupted() {
        return cancelled;
    }
}
