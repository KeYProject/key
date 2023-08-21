/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.StopCondition;

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
public final class AppliedRuleStopCondition implements StopCondition {
    /**
     * {@inheritDoc}
     */
    @Override
    public int getMaximalWork(int maxApplications, long timeout, Proof proof) {
        return maxApplications;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isGoalAllowed(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, Goal goal) {
        return true; // Default behavior is to accept all rules.
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getGoalNotAllowedMessage(int maxApplications, long timeout, Proof proof,
            long startTime, int countApplied, Goal goal) {
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean shouldStop(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
        return countApplied >= maxApplications
                || timeout >= 0 && System.currentTimeMillis() - startTime >= timeout;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStopMessage(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo) {
        return "Maximal number of rule applications reached or timed out.";
    }
}
