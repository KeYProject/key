// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableHeap;
import org.key_project.util.collection.ImmutableLeftistHeap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Implementation of {@link AutomatedRuleApplicationManager} that stores
 * possible {@link RuleApp}s in a priority queue. The element with highest
 * priority in the queue can be obtained via {@link #next()}. This operation
 * will remove the element from the queue. The priority of a given
 * {@link RuleApp} corresponds to its {@link RuleAppCost}. A {@link RuleApp} can
 * be equipped with a {@link RuleAppCost} by converting it into a
 * {@link RuleAppContainer}. The cost of a {@link RuleApp} is computed according
 * to a given {@link Strategy} (see
 * {@link Strategy#computeCost(RuleApp, PosInOccurrence, Goal)}).
 */
public class QueueRuleApplicationManager implements AutomatedRuleApplicationManager {

    /**
     * The goal this manager belongs to.
     */
    private Goal goal = null;

    /**
     * Priority queue containing all {@link RuleAppContainer}s that are candidates
     * for application on a {@link Goal}.
     */
    private ImmutableHeap<RuleAppContainer> queue = null;

    /**
     * The minimum {@link RuleAppContainer} from a previous round. It is taken
     * out of queue temporarily and is put back in during the next round. After
     * all, the corresponding rule still needs to be taken into consideration
     * for future rule applications.
     */
    private RuleAppContainer previousMinimum = null;

    /**
     * The next automatic {@link RuleApp} determined by the strategy. Aka result
     * of methods {@link #next()} and {@link #peekNext()}.
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
     * Add all rules to the heap that are not reported via the
     * <code>RuleListener</code> connection
     */
    private void ensureQueueExists() {
        if (queue != null) {
            return;
        }

        /*
         * If no goal is specified, we cannot assign a value to the queue. In
         * that case clear the cache and return.
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
        goal.ruleAppIndex().reportAutomatedRuleApps(goal.getRuleAppManager(), goal.proof().getServices());
    }

    /**
     * Implementation of the method from <code>NewRuleListener</code>. The new
     * rule app is added to the heap
     */
    @Override
    public void ruleAdded(RuleApp rule, PosInOccurrence pos) {
        if (queue == null) {
            // then the heap has to be rebuilt completely anyway, and the new
            // rule app is not of interest for us
            return;
        }

        RuleAppContainer c = RuleAppContainer.createAppContainer(rule, pos, goal);
        ensureQueueExists();
        queue = push(c, queue);
    }

    /**
     * Implementation of the method from <code>NewRuleListener</code>. The new
     * rule app is added to the heap
     */
    @Override
    public void rulesAdded(ImmutableList<? extends RuleApp> rules, PosInOccurrence pos) {
        if (queue == null) {
            // then the heap has to be rebuilt completely anyway, and the new
            // rule app is not of interest for us
            return;
        }

        final ImmutableList<RuleAppContainer> containers = RuleAppContainer.createAppContainers(rules, pos, goal);
        ensureQueueExists();
        for (RuleAppContainer rac : containers) {
            queue = push(rac, queue);
        }
    }

    /**
     * Add a number of new rule apps to the heap
     */
    private ImmutableHeap<RuleAppContainer> push(Iterator<RuleAppContainer> it,
            ImmutableHeap<RuleAppContainer> sourceQueue) {
        while (it.hasNext()) {
            sourceQueue = push(it.next(), sourceQueue);
        }
        return sourceQueue;
    }

    /**
     * Add a new rule app to the heap, provided that the rule app is not
     * infinitely expensive
     */
    private ImmutableHeap<RuleAppContainer> push(RuleAppContainer c, ImmutableHeap<RuleAppContainer> sourceQueue) {
        if (c.getCost() instanceof TopRuleAppCost) {
            return sourceQueue;
        } else {
            return sourceQueue.insert(c);
        }
    }

    /**
     * @return the first applicable rule app, i.e. the least expensive element
     *         of the heap that is not obsolete and caches the result of this
     *         operation to save some time the next time the method
     *         nextAndCache() or next() is called. A call of next() empties the
     *         cache again.
     */
    @Override
    public RuleApp peekNext() {
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
         * Create further appcontainers from previous minimum, which was removed
         * from queue in a previous round.
         */
        ImmutableHeap<RuleAppContainer> furtherAppsQueue = ImmutableLeftistHeap.nilHeap();
        if (previousMinimum != null) {
            furtherAppsQueue = push(previousMinimum.createFurtherApps(goal).iterator(), furtherAppsQueue);
            previousMinimum = null;
        }

        clearNextRuleApp();
        computeNextRuleApp(furtherAppsQueue);
        return nextRuleApp;
    }

    /**
     * @return the first applicable rule app, i.e. the least expensive element
     *         of the heap that is not obsolete
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
     * Helper method for {@link #peekNext()}. Searches for the next rule
     * application, at which the iteration includes all rule app containers that
     * are contained either in primary or secondary queue.
     */
    private void computeNextRuleApp(ImmutableHeap<RuleAppContainer> furtherAppsQueue) {
        /*
         * Working list contains rule apps that cannot be completed in the
         * current round but will be reconsidered during the next round.
         */
        ImmutableList<RuleAppContainer> workingList = ImmutableSLList.nil();

        /**
         * Try to find a rule app that can be completed until both queues are
         * exhausted.
         */
        while (nextRuleApp == null && !(queue.isEmpty() && furtherAppsQueue.isEmpty())) {

            /*
             * Determine the minimum rule app container, ranging over both
             * queues. Putting this into a separate method would be convenient.
             * But since we are using immutable data structures, this cannot be
             * done very elegantly.
             */
            final RuleAppContainer minRuleAppContainer;
            final boolean furtherAppsQueueUsed;
            if (queue.isEmpty()) {
                // Use furtherAppsQueue in case queue is empty.
                furtherAppsQueueUsed = true;
                minRuleAppContainer = furtherAppsQueue.findMin();
                furtherAppsQueue = furtherAppsQueue.deleteMin();
            } else if (furtherAppsQueue.isEmpty()) {
                // Use queue in case furtherAppsQueueUsed is empty.
                furtherAppsQueueUsed = false;
                minRuleAppContainer = queue.findMin();
                queue = queue.deleteMin();
            } else {
                // Neither queue is empty. Find a minimum that ranges over both
                // queues.
                RuleAppContainer queueMin = queue.findMin();
                RuleAppContainer furtherAppsQueueMin = furtherAppsQueue.findMin();
                furtherAppsQueueUsed = queueMin.compareTo(furtherAppsQueueMin) > 0;
                if (furtherAppsQueueUsed) {
                    furtherAppsQueue = furtherAppsQueue.deleteMin();
                    minRuleAppContainer = furtherAppsQueueMin;
                } else {
                    queue = queue.deleteMin();
                    minRuleAppContainer = queueMin;
                }
            }

            nextRuleApp = minRuleAppContainer.completeRuleApp(goal);
            /**
             * The obtained minimum rule app container was removed from the
             * queue it came from. The following if-then-else block makes sure
             * that {@link TacletAppContainer}s do not go missing so that
             * further apps can be created from it in future rounds.
             */
            if (nextRuleApp == null && minRuleAppContainer instanceof TacletAppContainer) {
                /**
                 * Cannot complete given {@link TacletAppContainer}, attempt
                 * resulted in null.
                 */
                if (furtherAppsQueueUsed) {
                    /*
                     * Put into working list if found in furtherAppsQueue. The
                     * rule app container will be reused in next round.
                     */
                    workingList = workingList.prepend(minRuleAppContainer);
                } else {
                    /*
                     * Create further apps if found in main queue. Rule apps
                     * obtained this way will be considered during the current
                     * round.
                     */
                    furtherAppsQueue = push(minRuleAppContainer.createFurtherApps(goal).iterator(), furtherAppsQueue);
                }
            } else {
                /*
                 * Found a suitable rule application. It will be memorized so
                 * that further apps can be created from it at the beginning of
                 * next round.
                 */
                previousMinimum = minRuleAppContainer;
            }
        }
        /*
         * Put remaining elements into main queue, so they can be considered in
         * the upcoming rounds.
         */
        queue = queue.insert(workingList.iterator());
        queue = queue.insert(furtherAppsQueue);
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