/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.concurrent.atomic.AtomicLong;
import javax.annotation.Nullable;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

import org.key_project.util.collection.ImmutableHeap;
import org.key_project.util.collection.ImmutableLeftistHeap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Implementation of {@link AutomatedRuleApplicationManager} that stores possible {@link RuleApp}s
 * in a priority queue. The element with highest priority in the queue can be obtained via
 * {@link #next()}. This operation will remove the element from the queue. The priority of a given
 * {@link RuleApp} corresponds to its {@link RuleAppCost}. A {@link RuleApp} can be equipped with a
 * {@link RuleAppCost} by converting it into a {@link RuleAppContainer}. The cost of a
 * {@link RuleApp} is computed according to a given {@link Strategy} (see
 * {@link Strategy#computeCost(RuleApp, PosInOccurrence, Goal)}).
 */
public class QueueRuleApplicationManager implements AutomatedRuleApplicationManager {
    public static final AtomicLong PERF_QUEUE_OPS = new AtomicLong();
    public static final AtomicLong PERF_PEEK = new AtomicLong();
    public static final AtomicLong PERF_CREATE_CONTAINER = new AtomicLong();

    /**
     * The goal this manager belongs to.
     */
    private Goal goal = null;

    /**
     * Priority queue containing all {@link RuleAppContainer}s that are candidates for application
     * on a {@link Goal}.
     */
    private ImmutableHeap<RuleAppContainer> queue = null;

    /**
     * The minimum {@link RuleAppContainer} from a previous round. It is taken out of queue
     * temporarily and is put back in during the next round. After all, the corresponding rule still
     * needs to be taken into consideration for future rule applications.
     */
    private RuleAppContainer previousMinimum = null;

    /**
     * The next automatic {@link RuleApp} determined by the strategy. Aka result of methods
     * {@link #next()} and {@link #peekNext()}.
     */
    private RuleApp nextRuleApp = null;

    private long nextRuleTime;

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
        goal.ruleAppIndex().reportAutomatedRuleApps();
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
    public void rulesAdded(ImmutableList<? extends RuleApp> rules, PosInOccurrence pos) {
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
            ImmutableHeap<RuleAppContainer> furtherAppsQueue =
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
    private void computeNextRuleApp(ImmutableHeap<RuleAppContainer> furtherAppsQueue) {
        /*
         * Working list contains rule apps that cannot be completed in the current round but will be
         * reconsidered during the next round.
         */
        ImmutableList<RuleAppContainer> workingList = ImmutableSLList.nil();

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
                    var time = System.nanoTime();
                    try {
                        furtherAppsQueue =
                            push(minRuleAppContainer.createFurtherApps(goal).iterator(),
                                furtherAppsQueue);
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

    @Override
    public AutomatedRuleApplicationManager copy() {
        return (AutomatedRuleApplicationManager) clone();
    }

    @Override
    public Object clone() {
        QueueRuleApplicationManager res = new QueueRuleApplicationManager();
        res.queue = queue;
        res.previousMinimum = previousMinimum;
        return res;
    }

}
