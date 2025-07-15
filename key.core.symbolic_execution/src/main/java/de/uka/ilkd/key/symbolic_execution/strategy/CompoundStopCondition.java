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

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This {@link StopCondition} contains other {@link StopCondition} as children and stops the auto
 * mode if at least on of its children force it.
 *
 * @author Martin Hentschel
 */
@NullMarked
public class CompoundStopCondition implements StopCondition<Goal> {
    /**
     * The child {@link StopCondition}s to use.
     */
    private final List<StopCondition<Goal>> children = new LinkedList<>();

    /**
     * The last {@link StopCondition} treated in
     * {@link StopCondition#isGoalAllowed} which
     * will provide the reason via
     * {@link StopCondition#getGoalNotAllowedMessage}.
     */
    private @Nullable StopCondition<Goal> lastGoalAllowedChild = null;

    /**
     * The last {@link StopCondition} treated in {@link StopCondition#shouldStop},
     * which will provide the reason via {@link StopCondition#getStopMessage}.
     */
    private @Nullable StopCondition<Goal> lastShouldStopChild;

    /**
     * Constructor.
     *
     * @param children The child {@link StopCondition}s to use.
     */
    @SafeVarargs
    public CompoundStopCondition(StopCondition<Goal>... children) {
        Collections.addAll(this.children, children);
    }

    /**
     * Adds new child {@link StopCondition}s.
     *
     * @param children The child {@link StopCondition}s to use.
     */
    @SafeVarargs
    public final void addChildren(StopCondition<Goal>... children) {
        Collections.addAll(this.children, children);
    }

    public void removeChild(StopCondition<Goal> child) {
        children.remove(child);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getMaximalWork(int maxApplications, long timeout) {
        // Get maximal work on each child because they might use this method for initialization
        // purpose.
        for (StopCondition<Goal> child : children) {
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
    public boolean isGoalAllowed(@Nullable Goal goal, int maxApplications, long timeout,
            long startTime,
            int countApplied) {
        boolean allowed = true;
        Iterator<StopCondition<Goal>> childIter = children.iterator();
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
    public String getGoalNotAllowedMessage(@Nullable Goal goal, int maxApplications, long timeout,
            long startTime, int countApplied) {
        return lastGoalAllowedChild != null
                ? lastGoalAllowedChild.getGoalNotAllowedMessage(goal, maxApplications, timeout,
                    startTime, countApplied)
                : "Internal state. Method getGoalNotAllowedMessage called, but last allowed goal is null";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean shouldStop(int maxApplications, long timeout, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
        boolean stop = false;
        Iterator<StopCondition<Goal>> childIter = children.iterator();
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
    public @NonNull String getStopMessage(int maxApplications, long timeout, long startTime,
            int countApplied, @Nullable SingleRuleApplicationInfo singleRuleApplicationInfo) {
        return lastShouldStopChild != null
                ? lastShouldStopChild.getStopMessage(maxApplications, timeout, startTime,
                    countApplied, singleRuleApplicationInfo)
                : "";
    }

    public List<StopCondition<Goal>> getChildren() {
        return children;
    }
}
