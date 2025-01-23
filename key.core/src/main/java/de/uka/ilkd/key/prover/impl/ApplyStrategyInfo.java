/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

/**
 * The final result of the strategy application is stored in this container and returned to the
 * instance that started the strategies.
 * <p>
 * It contains statistic information about the number of applied rules, time needed or number of
 * closed goals. In case the rule application stopped at a non-closeable goal, this goal is also
 * stored to allow the caller to e.g. present it to the user for interaction.
 * </p>
 * In case of an unexpected, the thrown exception can be also retrieved from this container.
 */
public class ApplyStrategyInfo
        implements org.key_project.prover.engine.ApplyStrategyInfo<Proof, Goal> {
    private final String message;
    private final Goal nonCloseableGoal;

    private final Throwable error;

    private final long timeInMillis;
    private final int appliedRuleAppsCount;
    private final int nrClosedGoals;
    private final Proof proof;

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

    @Override
    public String reason() {
        return message;
    }

    @Override
    public Goal nonCloseableGoal() {
        return nonCloseableGoal;
    }

    @Override
    public boolean isError() {
        return error != null;
    }

    @Override
    public Throwable getException() {
        return error;
    }

    @Override
    public long getTime() {
        return timeInMillis;
    }

    @Override
    public int getClosedGoals() {
        return nrClosedGoals;
    }

    @Override
    public int getAppliedRuleApps() {
        return appliedRuleAppsCount;
    }

    @Override
    public Proof getProof() {
        return proof;
    }

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
