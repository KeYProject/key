/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.engine.SingleRuleApplicationInfo;
import org.key_project.prover.engine.StopCondition;

/**
 * This {@link StopCondition} contains other {@link StopCondition} as children and stops the auto
 * mode if at least on of its children force it.
 *
 * @author Martin Hentschel
 */
public class CompoundStopCondition implements StopCondition<Goal> {
    /**
     * The child {@link StopCondition}s to use.
     */
    private final List<StopCondition> children = new LinkedList<>();

    /**
     * The last {@link StopCondition} treated in
     * {@link StopCondition#isGoalAllowed} which
     * will provide the reason via
     * {@link StopCondition#getGoalNotAllowedMessage}.
     */
    private StopCondition lastGoalAllowedChild;

    /**
     * The last {@link StopCondition} treated in {@link StopCondition#shouldStop},
     * which will provide the reason via {@link StopCondition#getStopMessage}.
     */
    private StopCondition lastShouldStopChild;

    /**
     * Constructor.
     *
     * @param children The child {@link StopCondition}s to use.
     */
    public CompoundStopCondition(StopCondition... children) {
        Collections.addAll(this.children, children);
    }

    /**
     * Adds new child {@link StopCondition}s.
     *
     * @param children The child {@link StopCondition}s to use.
     */
    public void addChildren(StopCondition... children) {
        Collections.addAll(this.children, children);
    }

    public void removeChild(StopCondition child) {
        children.remove(child);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getMaximalWork(int maxApplications, long timeout) {
        // Get maximal work on each child because they might use this method for initialization
        // purpose.
        for (StopCondition child : children) {
            child.getMaximalWork(maxApplications, timeout);
        }
        lastGoalAllowedChild = null;
        lastShouldStopChild = null;
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isGoalAllowed(Goal goal, int maxApplications, long timeout, long startTime,
            int countApplied) {
        boolean allowed = true;
        Iterator<StopCondition> childIter = children.iterator();
        while (allowed && childIter.hasNext()) {
            lastGoalAllowedChild = childIter.next();
            allowed = lastGoalAllowedChild.isGoalAllowed(goal, maxApplications, timeout, startTime,
                countApplied);
        }
        return allowed;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getGoalNotAllowedMessage(Goal goal, int maxApplications, long timeout,
            long startTime, int countApplied) {
        return lastGoalAllowedChild != null ? lastGoalAllowedChild.getGoalNotAllowedMessage(
            goal, maxApplications, timeout, startTime, countApplied) : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean shouldStop(int maxApplications, long timeout, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
        boolean stop = false;
        Iterator<StopCondition> childIter = children.iterator();
        while (!stop && childIter.hasNext()) {
            lastShouldStopChild = childIter.next();
            stop = lastShouldStopChild.shouldStop(maxApplications, timeout, startTime,
                countApplied, singleRuleApplicationInfo);
        }
        return stop;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStopMessage(int maxApplications, long timeout, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
        return lastShouldStopChild != null
                ? lastShouldStopChild.getStopMessage(maxApplications, timeout, startTime,
                    countApplied, singleRuleApplicationInfo)
                : null;
    }

    public List<StopCondition> getChildren() {
        return children;
    }
}
