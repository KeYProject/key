package de.uka.ilkd.key.proof.runallproofs.performance;

public class RuleData {

    int numberInvocations = 1;
    long duration;

    public RuleData(long computeCostDuration) {
        this.duration = computeCostDuration;
    }

    public void addDuration(long duration) {
        numberInvocations++;
        this.duration += duration;
    }

}
