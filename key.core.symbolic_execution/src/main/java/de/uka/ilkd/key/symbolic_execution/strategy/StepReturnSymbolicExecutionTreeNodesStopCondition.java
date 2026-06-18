/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.engine.StopCondition;

/**
 * This {@link StopCondition} stops the auto mode when a "step over" is completed. This is the case
 * when the next symbolic execution tree node was executed on a {@link Goal} which has a lower stack
 * size as the symbolic execution tree node of the {@link Goal} on which the auto mode was started.
 *
 * @author Martin Hentschel
 */
public class StepReturnSymbolicExecutionTreeNodesStopCondition
        extends AbstractCallStackBasedStopCondition {
    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isCallStackSizeReached(int initialCallStackSize, int currentCallStackSize) {
        return currentCallStackSize < initialCallStackSize;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getGoalNotAllowedMessage(Goal goal, int maxApplications, long timeout,
            long startTime, int countApplied) {
        return "Step return completed.";
    }
}
