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
import org.key_project.util.collection.SingletonIterator;

import de.uka.ilkd.key.logic.BooleanContainer;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import static de.uka.ilkd.key.strategy.QueueRuleApplicationManager.QueueType.*;

public class QueueRuleApplicationManager implements AutomatedRuleApplicationManager {

    /** The goal this manager belongs to */
    private Goal goal = null;

    /**
     * The priority queue containing all possible next rule applications,
     * ordered by the costs the strategy object has assigned to them
     */
    private ImmutableHeap<RuleAppContainer> queue = null;

    private ImmutableHeap<RuleAppContainer> secondaryQueue = null;

    /**
     * The minimum {@link RuleAppContainer} from a previous round. It is taken
     * out of queue temporarily and is put back in during the next round. After
     * all, the corresponding rule still needs to be taken into consideration
     * for future rule applications.
     */
    private RuleAppContainer previousMinimum = null;

    public static enum QueueType {
        PRIMARY_QUEUE, SECONDARY_QUEUE
    }

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
        secondaryQueue = null;
        previousMinimum = null;
        TacletAppContainer.ifInstCache.reset(null);
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

        queue = ImmutableLeftistHeap.<RuleAppContainer> nilHeap();
        secondaryQueue = ImmutableLeftistHeap.<RuleAppContainer> nilHeap();
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

        final Iterator<RuleAppContainer> iterator = new SingletonIterator<RuleAppContainer>(
                RuleAppContainer.createAppContainer(rule, pos, goal, getStrategy()));
        ensureQueueExists();
        push(iterator, PRIMARY_QUEUE);
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

        final ImmutableList<RuleAppContainer> containers = RuleAppContainer.createAppContainers(rules, pos, goal,
                getStrategy());
        ensureQueueExists();
        for (RuleAppContainer rac : containers) {
            push(new SingletonIterator<RuleAppContainer>(rac), PRIMARY_QUEUE);
        }
    }

    /**
     * Add a number of new rule apps to the heap
     */
    private void push(Iterator<RuleAppContainer> it, QueueType target) {
        while (it.hasNext()) {
            push(it.next(), target);
        }
    }

    /**
     * Add a new rule app to the heap, provided that the rule app is not
     * infinitely expensive
     */
    private void push(RuleAppContainer c, QueueType target) {
        if (c.getCost() instanceof TopRuleAppCost) {
            return;
        }

        switch (target) {
        case PRIMARY_QUEUE:
            queue = queue.insert(c);
            break;
        case SECONDARY_QUEUE:
            secondaryQueue = secondaryQueue.insert(c);
            break;
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

        // Create further appcontainers from previous minimum, which was taken
        // out of queue.
        if (previousMinimum != null) {
            addFurtherAppsToSecondaryQueue(previousMinimum);
            previousMinimum = null;
        }

        clearNextRuleApp();
        computeNextRuleApp();
        queue = queue.insert(secondaryQueue);
        secondaryQueue = ImmutableLeftistHeap.nilHeap();
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
    private void computeNextRuleApp() {
        final BooleanContainer secondaryQueueUsed = new BooleanContainer();
        ImmutableList<RuleAppContainer> workingList = ImmutableSLList.nil();
        /**
         * Try to find a rule until both queues are exhausted.
         */
        while (nextRuleApp == null && !(queue.isEmpty() && secondaryQueue.isEmpty())) {
            RuleAppContainer minRuleAppContainer = getMinRuleAppContainer(secondaryQueueUsed);
            nextRuleApp = minRuleAppContainer.completeRuleApp(goal, getStrategy());
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
                if (secondaryQueueUsed.val()) {
                    /*
                     * Put into working list if found in secondary queue. The
                     * rule app container will be reused in next round.
                     */
                    workingList = workingList.prepend(minRuleAppContainer);
                } else {
                    /*
                     * Create further apps if found in primary queue. Rule apps
                     * obtained this way will be considered during the current
                     * round.
                     */
                    addFurtherAppsToSecondaryQueue(minRuleAppContainer);
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
         * Put working list elements into queue, so they can be considered in
         * the next round.
         */
        queue = queue.insert(workingList.iterator());
    }

    /**
     * Return the {@link RuleAppContainer} with minimum costs, at which both
     * primary and secondary queue entries are considered. The obtained
     * {@link RuleAppContainer} is removed from the corresponding queue.
     * 
     * @param usedSecondary
     *            The value of this container will indicate whether the returned
     *            minimum was obtained from first or secondary queue.
     * @return The rule app with minimum costs from secondary and primary queue.
     */
    private RuleAppContainer getMinRuleAppContainer(BooleanContainer usedSecondary) {
        // Use secondary queue in case normal queue is empty.
        if (queue.isEmpty()) {
            usedSecondary.setVal(true);
            final RuleAppContainer c = secondaryQueue.findMin();
            secondaryQueue = secondaryQueue.deleteMin();
            return c;
        }

        // Use normal queue in case secondary queue is empty.
        if (secondaryQueue.isEmpty()) {
            usedSecondary.setVal(false);
            final RuleAppContainer c = queue.findMin();
            queue = queue.deleteMin();
            return c;
        }

        /*
         * Neither queue is empty. Find a minimum that ranges over both queues
         * and return.
         */
        RuleAppContainer primaryQueueMin = queue.findMin();
        RuleAppContainer secondaryQueueMin = secondaryQueue.findMin();
        usedSecondary.setVal(primaryQueueMin.compareTo(secondaryQueueMin) > 0);
        if (usedSecondary.val()) {
            secondaryQueue = secondaryQueue.deleteMin();
            return secondaryQueueMin;
        } else {
            queue = queue.deleteMin();
            return primaryQueueMin;
        }
    }

    private void addFurtherAppsToSecondaryQueue(RuleAppContainer app) {
        push(app.createFurtherApps(goal, getStrategy()).iterator(), SECONDARY_QUEUE);
    }

    private Strategy getStrategy() {
        return goal.getGoalStrategy();
    }

    @Override
    public AutomatedRuleApplicationManager copy() {
        return (AutomatedRuleApplicationManager) clone();
    }

    @Override
    public Object clone() {
        QueueRuleApplicationManager res = new QueueRuleApplicationManager();
        res.queue = queue;
        res.secondaryQueue = secondaryQueue;
        res.previousMinimum = previousMinimum;
        return res;
    }

    /**
     * this rule app manager has no manager to delegate to but is the "base"
     * manager.
     */
    @Override
    public AutomatedRuleApplicationManager getDelegate() {
        return null;
    }

}