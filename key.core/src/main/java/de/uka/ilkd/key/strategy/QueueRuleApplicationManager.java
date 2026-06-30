/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.FormulaChangeInfo;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentChangeInfo;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.RuleApplicationManager;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.collection.ImmutableHeap;
import org.key_project.util.collection.ImmutableLeftistHeap;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Implementation of {@link RuleApplicationManager} that stores possible {@link RuleApp}s
 * in a priority queue. The element with highest priority in the queue can be obtained via
 * {@link #next()}. This operation will remove the element from the queue. The priority of a given
 * {@link RuleApp} corresponds to its {@link RuleAppCost}. A {@link RuleApp} can be equipped with a
 * {@link RuleAppCost} by converting it into a {@link RuleAppContainer}. The cost of a
 * {@link RuleApp} is computed according to a given {@link Strategy} (see
 * {@link Feature#computeCost(RuleApp, PosInOccurrence, ProofGoal, MutableState)}).
 */
@NullMarked
public class QueueRuleApplicationManager implements RuleApplicationManager<Goal> {
    public static final AtomicLong PERF_QUEUE_OPS = new AtomicLong();
    public static final AtomicLong PERF_PEEK = new AtomicLong();
    public static final AtomicLong PERF_CREATE_CONTAINER = new AtomicLong();

    /**
     * The goal this manager belongs to.
     */
    private @Nullable Goal goal = null;

    /**
     * Priority queue containing all {@link RuleAppContainer}s that are candidates for application
     * on a {@link Goal}.
     */
    private @Nullable ImmutableHeap<RuleAppContainer> queue = null;

    /**
     * The minimum {@link RuleAppContainer} from a previous round. It is taken out of queue
     * temporarily and is put back in during the next round. After all, the corresponding rule still
     * needs to be taken into consideration for future rule applications.
     */
    private @Nullable RuleAppContainer previousMinimum = null;

    /**
     * The next automatic {@link RuleApp} determined by the strategy. Aka result of methods
     * {@link #next()} and {@link #peekNext()}.
     */
    private @Nullable RuleApp nextRuleApp = null;

    private long nextRuleTime;

    /**
     * Parked assumes-incomplete taclet bases, indexed by the concrete top operator(s) of their
     * {@code \assumes} formulas. Such bases re-expand to nothing (no new assumes match) on almost
     * every round (profiling: 96.8% of queue pops fail at the unmatched {@code \assumes}, and
     * 97-99.6% of the resulting re-expansions yield no new instance -- the dominant remaining queue
     * churn), so instead of re-popping and re-expanding them each round they are parked here and
     * woken only when a formula they could match appears. A base is stored under each of its wake
     * operators and woken when any of them is added/modified. Insertion-ordered for determinism;
     * {@code null} until the first base is parked.
     * <p>
     * Sound (byte-identical) by construction, unlike the earlier sequent-growth heuristic:
     * <ul>
     * <li>Only <em>effectively-indexable</em> bases are parked -- every {@code \assumes} formula's
     * top operator is concrete or a schema variable already bound by the find-match (see
     * {@link #assumesWakeOps}). Bases with an unbound-generic top (which would match any formula)
     * are never parked; they stay in the active queue and re-expand every round exactly as without
     * parking.</li>
     * <li>A parked base is woken (re-inserted into the active queue) on exactly the round a formula
     * with a matching top operator is added or modified ({@link #sequentChanged}/{@code
     * pendingWakeOps}) -- the same round its non-parked counterpart would first see that formula as
     * "new" and re-expand to the instance. So the instance enters the queue at the identical round,
     * with the identical (current) age and cost, and the proof is byte-identical.</li>
     * <li>The wake set is a sound <em>superset</em>: it walks the changed formula's update-prefix
     * spine of operators (the assumes matcher strips the update context before matching, see
     * {@code VMTacletMatcher.matchUpdateContext}). Over-waking is harmless -- a spuriously woken
     * base
     * is popped, re-expands to nothing, and is re-parked, exactly as a non-parked base would behave
     * that round. Only <em>missing</em> a wake would diverge, and that cannot happen for an
     * effectively-indexable base.</li>
     * <li>All structures are insertion-ordered ({@link LinkedHashMap}/{@link ArrayList}/
     * {@link LinkedHashSet}) so parking introduces no non-determinism.</li>
     * </ul>
     */
    // The per-operator buckets are plain ArrayLists, not sets, while small. A base is parked at
    // most
    // once per bucket (removed from all its buckets when woken; see unindexParked) and
    // RuleAppContainer uses identity equality, so there is nothing to de-duplicate -- whereas a set
    // would spend a whole LinkedHashMap (16-slot table + a 40-byte Entry per element) to hold a
    // handful of refs. A bucket that grows past {@link #BUCKET_SET_THRESHOLD} is switched to a
    // LinkedHashSet so the by-value unindexParked stays O(1) (see park).
    private @Nullable LinkedHashMap<Operator, Collection<RuleAppContainer>> parkedByOp = null;
    /**
     * Bucket size at which a per-operator parking bucket is promoted from ArrayList to
     * LinkedHashSet.
     */
    private static final int BUCKET_SET_THRESHOLD = 16;
    /**
     * Top operators (along the update-prefix spine) of formulas added/modified since the previous
     * round; the wake candidates consumed at the start of the next round. Insertion-ordered for
     * determinism; {@code null} until the first change is recorded.
     */
    private @Nullable LinkedHashSet<Operator> pendingWakeOps = null;

    @Override
    public void setGoal(Goal p_goal) {
        goal = p_goal;
    }

    /**
     * Clear the heap of applicable rules
     */
    @Override
    public void clearCache() {
        queue = null;
        previousMinimum = null;
        parkedByOp = null;
        pendingWakeOps = null;
        if (goal != null) {
            goal.proof().getServices().getCaches().getIfInstantiationCache().releaseAll();
        }
        clearNextRuleApp();
    }

    /**
     * Add all rules to the heap that are not reported via the <code>RuleListener</code> connection
     */
    private void ensureQueueExists() {
        if (queue != null) {
            return;
        }

        /*
         * If no goal is specified, we cannot assign a value to the queue. In that case clear the
         * cache and return.
         */
        if (goal == null) {
            clearCache();
            return;
        }

        queue = ImmutableLeftistHeap.nilHeap();
        previousMinimum = null;

        // to support encapsulating rule managers (delegation, like in
        // <code>FocussedRuleApplicationManager</code>) the rule index
        // reports its contents to the rule manager of the goal, which is not
        // necessarily this object
        goal.ruleAppIndex().reportAutomatedRuleApps(goal.getRuleAppManager(),
            goal.proof().getServices());
    }

    /**
     * Implementation of the method from <code>NewRuleListener</code>. The new rule app is added to
     * the heap
     */
    @Override
    public void ruleAdded(RuleApp rule, PosInOccurrence pos) {
        if (queue == null) {
            // then the heap has to be rebuilt completely anyway, and the new
            // rule app is not of interest for us
            return;
        }

        var time = System.nanoTime();
        RuleAppContainer c = RuleAppContainer.createAppContainer(rule, pos, goal);
        PERF_CREATE_CONTAINER.addAndGet(System.nanoTime() - time);

        ensureQueueExists();
        addRuleApp(c);
    }

    /**
     * Implementation of the method from <code>NewRuleListener</code>. The new rule app is added to
     * the heap
     */
    @Override
    public void rulesAdded(ImmutableList<? extends RuleApp> rules,
            PosInOccurrence pos) {
        if (queue == null) {
            // then the heap has to be rebuilt completely anyway, and the new
            // rule app is not of interest for us
            return;
        }

        var time = System.nanoTime();
        final ImmutableList<RuleAppContainer> containers =
            RuleAppContainer.createAppContainers(rules, pos, goal);
        PERF_CREATE_CONTAINER.addAndGet(System.nanoTime() - time);
        ensureQueueExists();
        for (RuleAppContainer rac : containers) {
            addRuleApp(rac);
        }
    }

    private void addRuleApp(RuleAppContainer rac) {
        var time = System.nanoTime();
        try {
            queue = push(rac, queue);
        } finally {
            PERF_QUEUE_OPS.addAndGet(System.nanoTime() - time);
        }
    }

    /**
     * Add a number of new rule apps to the heap
     */
    private static ImmutableHeap<RuleAppContainer> push(Iterator<RuleAppContainer> it,
            ImmutableHeap<RuleAppContainer> sourceQueue) {
        while (it.hasNext()) {
            sourceQueue = push(it.next(), sourceQueue);
        }
        return sourceQueue;
    }

    /**
     * Add a new rule app to the heap, provided that the rule app is not infinitely expensive
     */
    private static ImmutableHeap<RuleAppContainer> push(RuleAppContainer c,
            ImmutableHeap<RuleAppContainer> sourceQueue) {
        if (c.getCost() == TopRuleAppCost.INSTANCE) {
            return sourceQueue;
        } else {
            return sourceQueue.insert(c);
        }
    }

    private static ImmutableHeap<RuleAppContainer> createFurtherApps(
            @Nullable RuleAppContainer from, Goal goal) {
        if (from == null) {
            return ImmutableLeftistHeap.nilHeap();
        }
        var apps = from.createFurtherApps(goal);
        if (apps.isEmpty()) {
            return ImmutableLeftistHeap.nilHeap();
        }

        var actualApps = new ArrayList<RuleAppContainer>(apps.size());
        for (RuleAppContainer app : apps) {
            if (app.getCost() == TopRuleAppCost.INSTANCE) {
                continue;
            }
            actualApps.add(app);
        }
        var time = System.nanoTime();
        try {
            return ImmutableLeftistHeap.<RuleAppContainer>nilHeap().insert(actualApps.iterator());
        } finally {
            PERF_QUEUE_OPS.addAndGet(System.nanoTime() - time);
        }
    }

    /**
     * @return the first applicable rule app, i.e. the least expensive element of the heap that is
     *         not obsolete and caches the result of this operation to save some time the next time
     *         the method nextAndCache() or next() is called. A call of next() empties the cache
     *         again.
     */
    @Override
    public RuleApp peekNext() {
        var otime = System.nanoTime();
        try {
            ensureQueueExists();

            final long currentTime = goal.getTime();
            if (currentTime != nextRuleTime) {
                clearNextRuleApp();
                nextRuleTime = currentTime;
            }

            if (nextRuleApp != null) {
                return nextRuleApp;
            }

            goal.ruleAppIndex().fillCache();

            /*
             * Create further appcontainers from previous minimum, which was removed from queue in a
             * previous round.
             */
            ImmutableHeap<@NonNull RuleAppContainer> furtherAppsQueue =
                createFurtherApps(previousMinimum, goal);
            previousMinimum = null;

            computeNextRuleApp(furtherAppsQueue);
            return nextRuleApp;
        } finally {
            PERF_PEEK.addAndGet(System.nanoTime() - otime);
        }
    }

    /**
     * @return the first applicable rule app, i.e. the least expensive element of the heap that is
     *         not obsolete
     */
    @Override
    public RuleApp next() {
        final RuleApp res = peekNext();
        clearNextRuleApp();
        return res;
    }

    private void clearNextRuleApp() {
        nextRuleApp = null;
    }

    /**
     * Helper method for {@link #peekNext()}. Searches for the next rule application, at which the
     * iteration includes all rule app containers that are contained either in primary or secondary
     * queue.
     */
    private void computeNextRuleApp(ImmutableHeap<@NonNull RuleAppContainer> furtherAppsQueue) {
        /*
         * Working list contains rule apps that cannot be completed in the current round but will be
         * reconsidered during the next round.
         */
        ImmutableList<RuleAppContainer> workingList = ImmutableList.nil();

        // Wake parked assumes-bases whose \assumes top operator matches a formula added/modified
        // since the last round, re-inserting them into the active queue so they re-expand during
        // THIS
        // round -- the identical round their non-parked counterparts would first see that formula
        // as
        // new. No completeness net is needed (or wanted): an effectively-indexable base is always
        // woken on its matching round, and a late re-injection would surface its instance at the
        // wrong round, the very divergence parking must avoid.
        wakeParkedBases();

        /*
         * Try to find a rule app that can be completed until both queues are exhausted.
         */
        while (nextRuleApp == null && !(queue.isEmpty() && furtherAppsQueue.isEmpty())) {
            /*
             * Determine the minimum rule app container, ranging over both queues. Putting this into
             * a separate method would be convenient. But since we are using immutable data
             * structures, this cannot be done very elegantly.
             */
            final RuleAppContainer minRuleAppContainer;
            final boolean furtherAppsQueueUsed;
            if (queue.isEmpty()) {
                // Use furtherAppsQueue in case queue is empty.
                furtherAppsQueueUsed = true;
                var time = System.nanoTime();
                try {
                    minRuleAppContainer = furtherAppsQueue.findMin();
                    furtherAppsQueue = furtherAppsQueue.deleteMin();
                } finally {
                    PERF_QUEUE_OPS.addAndGet(System.nanoTime() - time);
                }
            } else if (furtherAppsQueue.isEmpty()) {
                // Use queue in case furtherAppsQueueUsed is empty.
                furtherAppsQueueUsed = false;
                var time = System.nanoTime();
                try {
                    minRuleAppContainer = queue.findMin();
                    queue = queue.deleteMin();
                } finally {
                    PERF_QUEUE_OPS.addAndGet(System.nanoTime() - time);
                }
            } else {
                // Neither queue is empty. Find a minimum that ranges over both
                // queues.
                var time = System.nanoTime();
                try {
                    RuleAppContainer queueMin = queue.findMin();
                    RuleAppContainer furtherAppsQueueMin = furtherAppsQueue.findMin();
                    assert (queueMin != null && furtherAppsQueueMin != null);
                    furtherAppsQueueUsed = queueMin.compareTo(furtherAppsQueueMin) > 0;
                    if (furtherAppsQueueUsed) {
                        furtherAppsQueue = furtherAppsQueue.deleteMin();
                        minRuleAppContainer = furtherAppsQueueMin;
                    } else {
                        queue = queue.deleteMin();
                        minRuleAppContainer = queueMin;
                    }
                } finally {
                    PERF_QUEUE_OPS.addAndGet(System.nanoTime() - time);
                }
            }

            nextRuleApp = minRuleAppContainer.completeRuleApp(goal);
            /*
             * The obtained minimum rule app container was removed from the queue it came from. The
             * following if-then-else block makes sure that {@link TacletAppContainer}s do not go
             * missing so that further apps can be created from it in future rounds.
             */
            if (nextRuleApp == null && minRuleAppContainer instanceof TacletAppContainer) {
                /*
                 * Cannot complete given {@link TacletAppContainer}, attempt resulted in null.
                 */
                if (furtherAppsQueueUsed) {
                    /*
                     * Put into working list if found in furtherAppsQueue. The rule app container
                     * will be reused in next round.
                     */
                    workingList = workingList.prepend(minRuleAppContainer);
                } else {
                    /*
                     * Create further apps if found in main queue. Rule apps obtained this way will
                     * be considered during the current round.
                     */
                    final ImmutableList<RuleAppContainer> further =
                        minRuleAppContainer.createFurtherApps(goal);
                    // Empty assumes yield (the re-expansion is just the re-costed base itself, with
                    // the now-current age): if the base is effectively indexable, park it instead
                    // of
                    // re-adding so it stops being re-popped every round. Park further.head() (the
                    // freshly re-costed container) so the parked age advances exactly as the
                    // non-parked base's would, keeping later assumes matches from re-deriving stale
                    // instances. A non-indexable base falls through and is re-added unchanged.
                    if (further.size() == 1
                            && further.head() instanceof TacletAppContainer base
                            && !base.getTacletApp().assumesInstantionsComplete()
                            && park(base)) {
                        continue;
                    }
                    var time = System.nanoTime();
                    try {
                        furtherAppsQueue = push(further.iterator(), furtherAppsQueue);
                    } finally {
                        PERF_QUEUE_OPS.addAndGet(System.nanoTime() - time);
                    }
                }
            } else {
                /*
                 * Found a suitable rule application. It will be memorized so that further apps can
                 * be created from it at the beginning of next round.
                 */
                previousMinimum = minRuleAppContainer;
            }
        }
        /*
         * Put remaining elements into main queue, so they can be considered in the upcoming rounds.
         */
        var time = System.nanoTime();
        try {
            queue = queue.insert(workingList.iterator());
            queue = queue.insert(furtherAppsQueue);
        } finally {
            PERF_QUEUE_OPS.addAndGet(System.nanoTime() - time);
        }
    }

    // ---------------------------------------------------------------------------------------------
    // Assumes-base parking (see parkedByOp)
    // ---------------------------------------------------------------------------------------------

    /**
     * Park an assumes-incomplete base, indexing it under the top operator(s) of its
     * {@code \assumes}
     * formulas so it can be woken when a matching formula appears.
     *
     * @param base the re-costed base container to park (carries the current age)
     * @return {@code true} if the base was parked; {@code false} if it is not effectively indexable
     *         (an unbound-generic {@code \assumes} top), in which case the caller must keep it in
     *         the
     *         active queue
     */
    private boolean park(TacletAppContainer base) {
        final List<Operator> ops = assumesWakeOps(base);
        if (ops == null) {
            return false;
        }
        if (parkedByOp == null) {
            parkedByOp = new LinkedHashMap<>();
        }
        for (Operator op : ops) {
            Collection<RuleAppContainer> bucket = parkedByOp.get(op);
            if (bucket == null) {
                bucket = new ArrayList<>(4);
                parkedByOp.put(op, bucket);
            }
            bucket.add(base);
            // unindexParked removes by value -- O(n) on a list. A few operators can collect
            // thousands of parked bases (e.g. the update operator on long straight-line proofs),
            // which would make wake/unpark O(n^2). Once a bucket grows past the threshold, switch
            // it
            // to a LinkedHashSet for O(1) removal; small buckets (the vast majority) stay
            // ArrayLists
            // for the memory saving. Both preserve insertion order, so the woken set is unchanged.
            if (bucket.size() == BUCKET_SET_THRESHOLD && bucket instanceof ArrayList) {
                parkedByOp.put(op, new LinkedHashSet<>(bucket));
            }
        }
        return true;
    }

    /**
     * Re-insert into the active queue every parked base waiting on an operator that was added or
     * modified since the previous round (see {@link #pendingWakeOps}). Woken bases are collected in
     * insertion order (deterministic) and removed from all their index buckets.
     */
    private void wakeParkedBases() {
        if (pendingWakeOps == null) {
            return;
        }
        if (parkedByOp != null && !parkedByOp.isEmpty()) {
            LinkedHashSet<RuleAppContainer> woken = null;
            for (Operator op : pendingWakeOps) {
                final Collection<RuleAppContainer> bucket = parkedByOp.get(op);
                if (bucket != null) {
                    if (woken == null) {
                        woken = new LinkedHashSet<>();
                    }
                    woken.addAll(bucket);
                }
            }
            if (woken != null) {
                for (RuleAppContainer c : woken) {
                    unindexParked(c);
                }
                var time = System.nanoTime();
                try {
                    queue = queue.insert(woken.iterator());
                } finally {
                    PERF_QUEUE_OPS.addAndGet(System.nanoTime() - time);
                }
            }
        }
        pendingWakeOps.clear();
    }

    /** Remove a woken container from every operator bucket it was parked under. */
    private void unindexParked(RuleAppContainer c) {
        if (parkedByOp == null || !(c instanceof TacletAppContainer tac)) {
            return;
        }
        final List<Operator> ops = assumesWakeOps(tac);
        if (ops == null) {
            return;
        }
        for (Operator op : ops) {
            final Collection<RuleAppContainer> bucket = parkedByOp.get(op);
            if (bucket != null) {
                bucket.remove(c);
                if (bucket.isEmpty()) {
                    parkedByOp.remove(op);
                }
            }
        }
    }

    /**
     * The concrete top operator(s) of the {@code \assumes} formulas of the given base, resolved
     * through the find-match's schema-variable instantiations.
     *
     * @return the wake operators, or {@code null} if the base is <em>not</em> effectively indexable
     *         -- i.e. some {@code \assumes} formula has a top that is an unbound schema variable
     *         (it
     *         would match any formula, so no precise wake operator exists) or has no
     *         {@code \assumes}
     *         formulas at all
     */
    private static @Nullable List<Operator> assumesWakeOps(TacletAppContainer base) {
        final NoPosTacletApp app = base.getTacletApp();
        final Sequent assumesSeq = app.taclet().assumesSequent();
        if (assumesSeq.isEmpty()) {
            return null;
        }
        final SVInstantiations insts = app.instantiations();
        final List<Operator> ops = new ArrayList<>(assumesSeq.size());
        for (SequentFormula sf : assumesSeq) {
            Operator op = sf.formula().op();
            if (op instanceof SchemaVariable sv) {
                final Object inst = insts.getInstantiation(sv);
                if (!(inst instanceof JTerm instTerm)) {
                    return null; // unbound (or non-term) generic top -> not indexable
                }
                op = instTerm.op();
                if (op instanceof SchemaVariable) {
                    return null; // still schematic -> not indexable
                }
            }
            ops.add(op);
        }
        return ops;
    }

    /**
     * Record, for the next round's wake-up, the top operators of every formula added or modified by
     * this sequent change. The assumes matcher strips the update context before matching, so the
     * whole update-prefix spine of each changed formula is recorded -- a sound superset of the
     * operators a parked base could match (see {@link #parkedByOp}). Called by {@code Goal} on
     * every
     * sequent change.
     */
    public void sequentChanged(SequentChangeInfo sci) {
        recordWakeOps(sci.addedFormulas(true));
        recordWakeOps(sci.addedFormulas(false));
        recordModifiedWakeOps(sci.modifiedFormulas(true));
        recordModifiedWakeOps(sci.modifiedFormulas(false));
    }

    private void recordWakeOps(ImmutableList<SequentFormula> added) {
        for (SequentFormula sf : added) {
            recordSpineOps(sf.formula());
        }
    }

    private void recordModifiedWakeOps(ImmutableList<FormulaChangeInfo> modified) {
        for (FormulaChangeInfo fci : modified) {
            recordSpineOps(fci.newFormula().formula());
        }
    }

    /** Add the operators along a formula's update-application spine to {@link #pendingWakeOps}. */
    private void recordSpineOps(org.key_project.logic.Term formula) {
        if (pendingWakeOps == null) {
            pendingWakeOps = new LinkedHashSet<>();
        }
        org.key_project.logic.Term t = formula;
        while (true) {
            final Operator op = t.op();
            pendingWakeOps.add(op);
            if (op instanceof UpdateApplication && t instanceof JTerm jt) {
                t = UpdateApplication.getTarget(jt);
            } else {
                break;
            }
        }
    }

    @Override
    public RuleApplicationManager<Goal> copy() {
        // noinspection unchecked
        return (RuleApplicationManager<Goal>) clone();
    }

    @Override
    public Object clone() {
        QueueRuleApplicationManager res = new QueueRuleApplicationManager();
        res.queue = queue;
        res.previousMinimum = previousMinimum;
        // the parking structures are mutable and goal-local: deep-copy so split goals park/wake
        // independently (the contained containers and operators are immutable and shared)
        if (parkedByOp != null) {
            final LinkedHashMap<Operator, Collection<RuleAppContainer>> copy =
                new LinkedHashMap<>(parkedByOp.size());
            for (Map.Entry<Operator, Collection<RuleAppContainer>> e : parkedByOp.entrySet()) {
                final Collection<RuleAppContainer> v = e.getValue();
                copy.put(e.getKey(),
                    v instanceof LinkedHashSet ? new LinkedHashSet<>(v) : new ArrayList<>(v));
            }
            res.parkedByOp = copy;
        }
        if (pendingWakeOps != null) {
            res.pendingWakeOps = new LinkedHashSet<>(pendingWakeOps);
        }
        return res;
    }

}
