/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine.impl;

import org.key_project.prover.engine.SingleRuleApplicationInfo;
import org.key_project.prover.engine.StopCondition;
import org.key_project.prover.proof.ProofGoal;

import org.jspecify.annotations.NonNull;

/**
 * <p>
 * Implementation of {@link StopCondition} which stops the strategy after a reached limit of rules
 * or after a timeout in ms.
 * </p>
 * <p>
 * This is the default {@link StopCondition} used during verification.
 * </p>
 *
 * @author Martin Hentschel
 */
public final class AppliedRuleStopCondition<Goal extends ProofGoal<@NonNull Goal>>
        implements StopCondition<Goal> {
    /**
     * {@inheritDoc}
     */
    @Override
    public int getMaximalWork(int maxApplications, long timeout) {
        return maxApplications;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isGoalAllowed(Goal goal, int maxApplications, long timeout, long startTime,
            int countApplied) {
        return true; // Default behavior is to accept all rules.
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getGoalNotAllowedMessage(Goal goal, int maxApplications, long timeout,
            long startTime, int countApplied) {
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean shouldStop(int maxApplications, long timeout, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
        return countApplied >= maxApplications
                || timeout >= 0 && System.currentTimeMillis() - startTime >= timeout;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStopMessage(int maxApplications, long timeout, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
        return "Maximal number of rule applications reached or timed out.";
    }
}
