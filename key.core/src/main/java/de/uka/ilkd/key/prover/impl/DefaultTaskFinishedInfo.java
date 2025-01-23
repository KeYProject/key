/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.engine.TaskFinishedInfo;

public class DefaultTaskFinishedInfo implements TaskFinishedInfo {

    /**
     * The task that has finished. May be one of:
     * <ul>
     * <li>{@link de.uka.ilkd.key.macros.ProofMacro}</li>
     * <li>{@link de.uka.ilkd.key.prover.impl.ApplyStrategy}</li>
     * <li>{@code de.uka.ilkd.key.core.KeYMediator} (when pruning)</li>
     * <li>{@code de.uka.ilkd.key.gui.mergerule.MergeRuleMenuItem}
     * (when applying a merge rule)</li>
     * <li>{@link de.uka.ilkd.key.proof.io.AbstractProblemLoader} (when loading a proof)</li>
     * </ul>
     *
     * @return the source
     */
    private final Object source;

    // TODO
    // can be Throwable or ApplyStrategyInfo
    private final Object result;
    private final Proof proof;
    private final long timeInMillis;
    private final int appliedRules;
    private final int closedGoals;


    /**
     * Create a new info object.
     * Make sure your source object is documented in {@link TaskFinishedInfo}!
     *
     * @param source source object
     * @param result task result
     * @param proof the proof the task worked on
     * @param time time the task took (milliseconds)
     * @param appliedRules how many nodes were created
     * @param closedGoals how many goals were closed
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

    @Override
    public long getTime() {
        return timeInMillis;
    }

    @Override
    public Object getResult() {
        return result;
    }

    @Override
    public Object getSource() {
        return source;
    }

    @Override
    public int getAppliedRules() {
        return appliedRules;
    }

    @Override
    public int getClosedGoals() {
        return closedGoals;
    }

    @Override
    public Proof getProof() {
        return proof;
    }

    // display message for the status bar
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
