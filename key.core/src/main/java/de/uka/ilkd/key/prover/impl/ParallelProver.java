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
import java.util.concurrent.atomic.AtomicInteger;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
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
 * Experimental goal-level parallel prover, gated behind {@code -Dkey.prover.parallel}.
 *
 * <p>
 * One worker thread per available goal: a {@link GoalScheduler} hands out open goals to a pool of
 * workers; each worker applies rules to its goal and offers the resulting subgoals back to the
 * scheduler. The run finishes when the scheduler becomes quiescent (no goal available and none in
 * flight) or a stop condition fires. Non-proving listeners are suspended for the whole run
 * (Phase 1). Fresh names need no per-worker treatment: minting searches the goal-local
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
 * Worker count comes from {@code -Dkey.prover.parallel.threads} (default 1).
 *
 * @author Claude (KeY multithreading effort)
 */
public final class ParallelProver extends DefaultProver<Proof, Goal> {

    private static final Logger LOGGER = LoggerFactory.getLogger(ParallelProver.class);

    /** When {@code true}, the auto-prover selection seam builds a {@link ParallelProver}. */
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

    /** Set once a stop condition fires; the first message wins. */
    private volatile @Nullable String stopMessage;
    private volatile boolean stopRequested;

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
     * The effective worker count. As with {@link #isEnabled()}, the {@link #THREADS_PROPERTY}
     * overrides the setting (and is honoured exactly, allowing the over-subscription the stress
     * tests
     * rely on); the setting-derived count is clamped to the available processors.
     */
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

    @Override
    public ApplyStrategyInfo<Proof, Goal> start(Proof proof, ImmutableList<Goal> goals,
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
        this.stopRequested = false;
        this.stopMessage = null;
        this.nonCloseableGoal = null;

        fireTaskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Strategy,
            PROCESSING_STRATEGY, maxApplications));

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

        final int poolId = POOL_COUNTER.incrementAndGet();
        final ExecutorService pool = Executors.newFixedThreadPool(workerCount, r -> {
            Thread t = new Thread(r, "key-prover-" + poolId);
            t.setDaemon(true);
            return t;
        });

        @Nullable
        Throwable error = null;
        // While more than one worker runs, advertise that a multi-threaded run is active so that
        // rules not yet safe under concurrency (e.g. MergeRule) disable themselves.
        final RunScope mtScope;
        if (workerCount > 1) {
            final RunScope marker = enterMultiThreadedRun();
            // Seal the Java type model for the duration of the parallel run: no new type may be
            // registered while workers prove concurrently. Types are pre-registered at load time
            // (ProblemInitializer), so a stray lazy registration on the proving path now fails fast
            // (IllegalStateException) instead of racing the shared model.
            final JavaInfo javaInfo = proof.getServices().getJavaInfo();
            // Materialise the default execution context on this proof's (fresh) JavaInfo before
            // sealing, so the matcher reads it instead of registering it during the run.
            javaInfo.getDefaultExecutionContext();
            javaInfo.sealTypeRegistration();
            mtScope = () -> {
                javaInfo.unsealTypeRegistration();
                marker.close();
            };
        } else {
            mtScope = () -> {
            };
        }
        try (var ignored = proof.suspendNonEssentialListeners(); mtScope) {
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
                error = e.getCause() != null ? e.getCause() : e;
                LOGGER.warn("parallel proof run failed", error);
            } catch (InterruptedException e) {
                cancelled = true;
            } finally {
                // Stop the workers and WAIT for them to actually finish while the non-essential
                // (GUI) proof-tree listeners are STILL suspended by the enclosing
                // try-with-resources -- the inner finally runs before the resource is closed. If we
                // returned (and let the listeners be re-attached) while a worker was still
                // mid-step,
                // that worker would deliver a proofExpanded event into the live Swing proof-tree
                // model off the EDT and deadlock against it: the EDT holds the AWT tree lock and
                // wants the GUIProofTreeModel monitor, while the worker holds that monitor and
                // wants
                // the AWT tree lock. Setting stopRequested makes the workers leave their claim
                // loop;
                // shutdownNow unblocks any parked in the scheduler.
                stopRequested = true;
                pool.shutdownNow();
                awaitWorkerTermination(pool);
            }
        }

        // Publish the lock-free counters into the inherited fields for the result.
        countApplied = appliedSteps.get();
        closedGoals = closedCount.get();

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
     * Waits for the worker pool to terminate after {@link ExecutorService#shutdownNow()}. The wait
     * runs with the calling thread's interrupt status cleared (the run is often stopped by
     * interrupting this very thread, which would otherwise make {@code awaitTermination} return
     * immediately and defeat the purpose) and restores the status afterwards. The generous timeout
     * accommodates a worker that is mid-step (e.g. a large taclet match) when asked to stop; the
     * stop is cooperative, so it returns as soon as the last worker leaves its step.
     */
    private void awaitWorkerTermination(ExecutorService pool) {
        boolean wasInterrupted = Thread.interrupted();
        try {
            if (!pool.awaitTermination(WORKER_SHUTDOWN_TIMEOUT_SECONDS, TimeUnit.SECONDS)) {
                LOGGER.warn("parallel prover workers did not stop within {}s of a stop request",
                    WORKER_SHUTDOWN_TIMEOUT_SECONDS);
            }
        } catch (InterruptedException e) {
            wasInterrupted = true;
        }
        if (wasInterrupted) {
            Thread.currentThread().interrupt();
        }
    }

    /** A single worker: claim goals and process them until the queue is quiescent or stopped. */
    private void workerLoop(GoalScheduler<Goal> scheduler, Object commitLock,
            long startTime) {
        // Bind a per-worker name recorder so the rule executor's fresh-name proposals (made in the
        // lock-free compute phase) do not race on the shared one. Only relevant at >1 worker.
        Services.bindWorkerNameRecorder();
        try {
            Goal goal;
            while (!stopRequested && (goal = scheduler.claimOrAwait()) != null) {
                processStep(goal, scheduler, commitLock, startTime);
            }
        } catch (InterruptedException e) {
            cancelled = true;
            Thread.currentThread().interrupt();
        } finally {
            Services.unbindWorkerNameRecorder();
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
            if (stopRequested) {
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
            fireTaskProgress();

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

    /** Records the first stop reason and signals all workers to finish. */
    private void requestStop(String message, @Nullable Goal goal) {
        if (!stopRequested) {
            stopMessage = message;
            nonCloseableGoal = goal;
            stopRequested = true;
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
