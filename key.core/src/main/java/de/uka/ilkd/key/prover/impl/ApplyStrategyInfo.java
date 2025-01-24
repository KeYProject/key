/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;


/**
 * A container class representing the final result of a proof strategy application.
 *
 * <p>
 * This implementation of {@link org.key_project.prover.engine.ApplyStrategyInfo}
 * provides detailed statistical information about the proof process, such as the
 * number of applied rules, time taken, and the number of closed goals. It also
 * retains information about unresolved goals or exceptions encountered during
 * the strategy execution.
 * </p>
 *
 * <p>
 * Instances of this class are designed to be immutable and are returned to the
 * caller of the strategy application to provide insights or for user interaction.
 * </p>
 *
 * <p>
 * Key features include:
 * <ul>
 * <li>Tracking the time taken for the strategy execution.</li>
 * <li>Recording the number of applied rule applications and closed goals.</li>
 * <li>Providing details of unresolved goals and any errors encountered.</li>
 * </ul>
 * </p>
 *
 * @see org.key_project.prover.engine.ApplyStrategyInfo
 */
public class ApplyStrategyInfo
        implements org.key_project.prover.engine.ApplyStrategyInfo<Proof, Goal> {

    /**
     * The reason why the strategy stopped, for example, proof finished, maximal number of rule
     * applications reached etc.
     */
    private final String message;

    /**
     * One of the non-closeable goals that lead to termination of the strategy execution, if one
     * exists.
     */
    private final Goal nonCloseableGoal;

    /** The exception encountered during the strategy application, if any. */
    private final Throwable error;

    /** The total time taken for the strategy execution, in milliseconds. */
    private final long timeInMillis;

    /** The number of rule applications applied during the strategy execution. */
    private final int appliedRuleAppsCount;

    /** The number of goals that were successfully closed during the strategy execution. */
    private final int nrClosedGoals;

    /** The proof object associated with this strategy application. */
    private final Proof proof;

    /**
     * Constructs an {@code ApplyStrategyInfo} object with all necessary details
     * of the strategy execution.
     *
     * @param message the message explaining the reason for the termination of strategy execution
     * @param proof the proof object associated with the strategy execution
     * @param error the exception encountered during execution, or {@code null} if no error occurred
     * @param nonCloseableGoal the non-closeable goal, or {@code null} if all goals were closed
     * @param timeInMillis the total execution time in milliseconds
     * @param appliedRuleAppsCount the number of applied rule applications
     * @param nrClosedGoals the number of successfully closed goals
     */
    public ApplyStrategyInfo(String message, Proof proof, Throwable error, Goal nonCloseableGoal,
            long timeInMillis, int appliedRuleAppsCount, int nrClosedGoals) {
        this.message = message;
        this.proof = proof;
        this.error = error;
        this.nonCloseableGoal = nonCloseableGoal;
        this.timeInMillis = timeInMillis;
        this.appliedRuleAppsCount = appliedRuleAppsCount;
        this.nrClosedGoals = nrClosedGoals;
    }

    /** {@inheritDoc} */
    @Override
    public String reason() {
        return message;
    }

    /** {@inheritDoc} */
    @Override
    public Goal nonCloseableGoal() {
        return nonCloseableGoal;
    }

    /** {@inheritDoc} */
    @Override
    public boolean isError() {
        return error != null;
    }

    /** {@inheritDoc} */
    @Override
    public Throwable getException() {
        return error;
    }

    /** {@inheritDoc} */
    @Override
    public long getTime() {
        return timeInMillis;
    }

    /** {@inheritDoc} */
    @Override
    public int getNumberOfClosedGoals() {
        return nrClosedGoals;
    }

    /** {@inheritDoc} */
    @Override
    public int getNumberOfAppliedRuleApps() {
        return appliedRuleAppsCount;
    }

    /** {@inheritDoc} */
    @Override
    public Proof getProof() {
        return proof;
    }

    /**
     * Provides a string representation of this {@code ApplyStrategyInfo} object,
     * including all key details such as message, error status, applied rules,
     * execution time, and closed goals.
     *
     * @return a string summarizing the state of this {@code ApplyStrategyInfo} object
     */
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Apply Strategy Info:");
        sb.append("\n Message: ").append(message);
        sb.append("\n Error:").append(isError());
        if (isError()) {
            sb.append("\n ").append(error.getMessage());
        }
        sb.append("\n Applied Rules: ").append(appliedRuleAppsCount);
        sb.append("\n Time: ").append(timeInMillis);
        sb.append("\n Closed Goals: ").append(nrClosedGoals);
        return sb.toString();
    }

}
