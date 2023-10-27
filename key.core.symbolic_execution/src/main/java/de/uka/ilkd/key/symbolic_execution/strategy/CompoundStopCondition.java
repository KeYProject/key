/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.StopCondition;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.prover.impl.SingleRuleApplicationInfo;

/**
 * This {@link StopCondition} contains other {@link StopCondition} as children and stops the auto
 * mode if at least on of its children force it.
 *
 * @author Martin Hentschel
 */
public class CompoundStopCondition implements StopCondition {
    /**
     * The child {@link StopCondition}s to use.
     */
    private final List<StopCondition> children = new LinkedList<>();

    /**
     * The last {@link StopCondition} treated in
     * {@link #isGoalAllowed(ApplyStrategy, int, long, Proof, GoalChooser, long, int, Goal)} which
     * will provide the reason via
     * {@link #getGoalNotAllowedMessage(ApplyStrategy, int, long, Proof, GoalChooser, long, int, Goal)}.
     */
    private StopCondition lastGoalAllowedChild;

    /**
     * The last {@link StopCondition} treated in
     * {@link #shouldStop(ApplyStrategy, int, long, Proof, GoalChooser, long, int, SingleRuleApplicationInfo)}
     * which will provide the reason via
     * {@link #getStopMessage(ApplyStrategy, int, long, Proof, GoalChooser, long, int, SingleRuleApplicationInfo)}.
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
    public int getMaximalWork(int maxApplications, long timeout, Proof proof) {
        // Get maximal work on each child because they might use this method for initialization
        // purpose.
        for (StopCondition child : children) {
            child.getMaximalWork(maxApplications, timeout, proof);
        }
        lastGoalAllowedChild = null;
        lastShouldStopChild = null;
        return 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, Goal goal) {
        boolean allowed = true;
        Iterator<StopCondition> childIter = children.iterator();
        while (allowed && childIter.hasNext()) {
            lastGoalAllowedChild = childIter.next();
            allowed = lastGoalAllowedChild.isGoalAllowed(maxApplications, timeout, proof, startTime,
                countApplied, goal);
        }
        return allowed;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getGoalNotAllowedMessage(int maxApplications, long timeout, Proof proof,
            long startTime, int countApplied, Goal goal) {
        return lastGoalAllowedChild != null ? lastGoalAllowedChild.getGoalNotAllowedMessage(
            maxApplications, timeout, proof, startTime, countApplied, goal) : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean shouldStop(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
        boolean stop = false;
        Iterator<StopCondition> childIter = children.iterator();
        while (!stop && childIter.hasNext()) {
            lastShouldStopChild = childIter.next();
            stop = lastShouldStopChild.shouldStop(maxApplications, timeout, proof, startTime,
                countApplied, singleRuleApplicationInfo);
        }
        return stop;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStopMessage(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
        return lastShouldStopChild != null
                ? lastShouldStopChild.getStopMessage(maxApplications, timeout, proof, startTime,
                    countApplied, singleRuleApplicationInfo)
                : null;
    }

    public List<StopCondition> getChildren() {
        return children;
    }
}
