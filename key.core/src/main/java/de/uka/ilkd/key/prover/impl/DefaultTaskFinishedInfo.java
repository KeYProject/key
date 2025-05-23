/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.engine.TaskFinishedInfo;

/**
 * A concrete implementation of the {@link TaskFinishedInfo} interface. This class holds
 * additional information about a task that has been completed, including the source,
 * result, proof, execution time, the number of applied rules, and closed goals.
 *
 * <p>
 * This implementation is used to track task completion details about the proof search.
 * </p>
 *
 * <p>
 * The task result may either be an exception (e.g., a {@link Throwable}) or
 * specific information about the proof search (strategy execution, proof macros or similar).
 * </p>
 */
public class DefaultTaskFinishedInfo implements TaskFinishedInfo {

    /**
     * The task that has finished. This can be one of several possible sources:
     * <ul>
     * <li>{@link de.uka.ilkd.key.macros.ProofMacro}</li>
     * <li>{@link ApplyStrategy}</li>
     * <li>{@code de.uka.ilkd.key.core.KeYMediator} (when pruning)</li>
     * <li>{@code de.uka.ilkd.key.gui.mergerule.MergeRuleMenuItem}
     * (when applying a merge rule)</li>
     * <li>{@link de.uka.ilkd.key.proof.io.AbstractProblemLoader} (when loading a proof)</li>
     * </ul>
     *
     * @return the source
     */
    private final Object source;

    // The result of the task, which can be either a Throwable or ApplyStrategyInfo.
    private final Object result;

    // The proof the task worked on.
    private final Proof proof;

    // Time taken to complete the task, in milliseconds.
    private final long timeInMillis;

    // Number of rules applied during the task.
    private final int appliedRules;

    // Number of goals closed during the task.
    private final int closedGoals;


    /**
     * Constructs a new {@link DefaultTaskFinishedInfo} object with the provided details.
     *
     * @param source The source object that initiated the task.
     * @param result The result of the task execution.
     * @param proof The proof worked on by the task.
     * @param time The time taken for the task to complete, in milliseconds.
     * @param appliedRules The number of rules applied during the task.
     * @param closedGoals The number of goals closed during the task.
     */
    public DefaultTaskFinishedInfo(Object source, Object result, Proof proof, long time,
            int appliedRules, int closedGoals) {
        this.source = source;
        this.result = result;
        this.proof = proof;
        this.timeInMillis = time;
        this.appliedRules = appliedRules;
        this.closedGoals = closedGoals;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public long getTime() {
        return timeInMillis;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object getResult() {
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object getSource() {
        return source;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getAppliedRules() {
        return appliedRules;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getClosedGoals() {
        return closedGoals;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Proof getProof() {
        return proof;
    }

    /**
     * Returns a string representation of the task's status. This message is typically used
     * for displaying in a status bar.
     *
     * <p>
     * The message includes details about the number of rules applied, the time taken,
     * the number of goals closed, and the number of remaining open goals.
     * </p>
     *
     * @return A status message summarizing the task's execution details.
     */
    @Override
    public String toString() {
        if (proof.isDisposed()) {
            return "Proof disposed";
        }
        if (appliedRules != 0) {
            StringBuilder message = new StringBuilder();
            String timeString = (timeInMillis / 1000) + "." + ((timeInMillis % 1000) / 100);

            message.append("Strategy: Applied ").append(appliedRules).append(" rule");
            if (appliedRules != 1) {
                message.append("s");
            }
            message.append(" (").append(timeString).append(" sec), ");
            message.append(" closed ").append(closedGoals).append(" goal");
            if (closedGoals != 1) {
                message.append("s");
            }
            message.append(", ").append(proof.openGoals().size());
            message.append(" remaining");
            return message.toString();
        } else {
            return "No rules applied";
        }
    }
}
