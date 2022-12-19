/**
 *
 */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.TaskFinishedInfo;

public class DefaultTaskFinishedInfo implements TaskFinishedInfo {

    private final Object source;

    // TODO
    // can be Throwable or ApplyStrategyInfo
    private final Object result;
    private final Proof proof;
    private final long timeInMillis;
    private final int appliedRules;
    private final int closedGoals;


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
