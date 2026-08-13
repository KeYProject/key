/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.FormulaChangeInfo;
import org.key_project.prover.sequent.PosInOccurrence;
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
 * {@link RuleApp} is computed according to a given {@link JavaStrategy} (see
 * {@link Feature#computeCost(RuleApp, PosInOccurrence, ProofGoal, MutableState)}).
 *
 * <h2>Why the set-aside state of this class belongs to one goal only</h2>
 *
 * Some vocabulary first. A {@link Goal} is one open branch of the proof, and its
 * {@code Sequent} is the collection of formulas that this branch currently consists of. The
 * automatic proof search runs in <em>rounds</em>: in each round it asks this manager for the next
 * rule application, performs it, and thereby changes the sequent. The <em>age</em> of a goal is
 * the number of rule applications performed on it so far ({@code Goal.getTime()}).
 *
 * <p>
 * A {@link RuleAppContainer} stores one possible rule application together with its cost, and the
 * cost includes the age the goal had when the container was created. The round in which a
 * container is created therefore decides its cost, the cost decides the order in which this
 * manager returns candidates, and that order decides which proof is found.
 *
 * <p>
 * Candidates that cannot be applied yet are set aside rather than kept in the queue, and are put
 * back in a later round (see {@link ParkedBases}). The round in which one is put back decides when
 * it
 * is created anew, and so, by the paragraph above, it decides the proof. This is why
 * the parking state ({@link ParkedBases}) belongs to a single goal: there is one manager per
 * goal, it is copied when a goal splits into two ({@link #clone()}), and it uses only collections
 * that keep insertion order ({@link LinkedHashMap}, {@link ArrayList}, {@link LinkedHashSet}).
 * A goal then sets aside and puts back candidates as a function of its own rule applications
 * alone, independent of how threads happen to be scheduled. That is what lets the prover find the
 * same proof whether it uses one worker thread or several.
 *
 * <p>
 * <strong>For anyone changing this class:</strong> this state must not be shared between goals,
 * and {@link #sequentChanged} must be called in the order in which the goal changed its sequent.
 * Sharing the state across goals, reusing candidates of one goal in another, or combining or
 * reordering {@code sequentChanged} calls changes ages, hence costs, hence proofs. Such a change
 * does not cause a crash, and a test that only checks whether a proof closes does not notice it.
 * {@code QueueRuleApplicationManagerParkingLocalityTest} checks that a copy shares no state with
 * its original. {@code ProofEquivalenceTest} and {@code MtDeterminismCiTest} check that several
 * worker threads find the same proof as one.
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
     * Candidates that are currently set aside because their {@code \assumes} formulas have no
     * match in the sequent yet, together with the machinery to file and wake them; see
     * {@link ParkedBases}. One instance per manager, replaced on {@link #clearCache()},
     * deep-copied on {@link #clone()}.
     */
    private ParkedBases parking = new ParkedBases();

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
        parking = new ParkedBases();
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

        // Put back every parked base that a formula added or changed since the last round could
        // match, so it re-expands in this round. This is the round in which an un-parked copy
        // would first see that formula as new (see the comment on the parking field).
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
                    // The re-expansion produced only the re-costed base itself: park it if it
                    // can be keyed, re-add it unchanged otherwise (see ParkedBases#park).
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
    // Assumes-base parking (see the parking field)
    // ---------------------------------------------------------------------------------------------

    /**
     * Set the given base aside; see {@link ParkedBases#park}.
     *
     * @return {@code true} if the base was parked, {@code false} if it cannot be parked and the
     *         caller must keep it in the queue
     */
    private boolean park(TacletAppContainer base) {
        return parking.park(base, goal);
    }

    /**
     * Put back into the queue every parked base that a formula changed since the previous round
     * could match; see {@link ParkedBases#drainWoken()}.
     */
    private void wakeParkedBases() {
        final Collection<RuleAppContainer> woken = parking.drainWoken();
        if (!woken.isEmpty()) {
            var time = System.nanoTime();
            try {
                queue = queue.insert(woken.iterator());
            } finally {
                PERF_QUEUE_OPS.addAndGet(System.nanoTime() - time);
            }
        }
    }

    /**
     * Called by {@code Goal} whenever it adds or changes a formula in the sequent. Records the
     * wake keys of each such formula (see {@link ParkedBases#recordWakeKeysOf}), so that
     * {@link #wakeParkedBases()} can wake the matching bases at the start of the next round.
     * <p>
     * The calls for one goal must arrive in the order in which that goal changed its sequent.
     * These records decide which bases are woken in which round, and so, as the class comment
     * explains, they decide the proof. Combining or reordering the calls would change the proof.
     */
    public void sequentChanged(SequentChangeInfo sci) {
        recordWakeKeys(sci.addedFormulas(true), true);
        recordWakeKeys(sci.addedFormulas(false), false);
        recordModifiedWakeKeys(sci.modifiedFormulas(true), true);
        recordModifiedWakeKeys(sci.modifiedFormulas(false), false);
    }

    private void recordWakeKeys(ImmutableList<SequentFormula> added, boolean inAntecedent) {
        for (SequentFormula sf : added) {
            parking.recordWakeKeysOf(sf.formula(), inAntecedent);
        }
    }

    private void recordModifiedWakeKeys(ImmutableList<FormulaChangeInfo> modified,
            boolean inAntecedent) {
        for (FormulaChangeInfo fci : modified) {
            parking.recordWakeKeysOf(fci.newFormula().formula(), inAntecedent);
        }
    }

    @Override
    public RuleApplicationManager<Goal> copy() {
        // noinspection unchecked
        return (RuleApplicationManager<Goal>) clone();
    }

    /**
     * Copies this manager when its goal splits into two. Each copy gets its own parking state
     * ({@link ParkedBases#copy()}), so that the two new goals park and wake independently. If
     * they shared this state, one goal waking a base would change the round in which it enters
     * the other goal's queue, and so change that goal's proof (see the class comment). The
     * stored {@link RuleAppContainer}s are never modified in place, so the copies may share
     * them. {@code QueueRuleApplicationManagerParkingLocalityTest} checks that this copy is
     * deep enough.
     */
    @Override
    public Object clone() {
        QueueRuleApplicationManager res = new QueueRuleApplicationManager();
        res.queue = queue;
        res.previousMinimum = previousMinimum;
        res.parking = parking.copy();
        return res;
    }

}
