package org.keyproject.key.api.data;

public record TaskStartedInfo() implements KeYDataTransferObject {
    public static TaskStartedInfo from(de.uka.ilkd.key.prover.TaskStartedInfo info) {
        return new TaskStartedInfo();
    }
}
