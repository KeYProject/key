package org.key_project.isabelletranslation;

import java.time.Duration;

public class IsabelleResult {
    public String getDescription() {
        return this.type.getDescription();
    }

    public Type getType() {
        return this.type;
    }

    public enum Type {
        SUCCESS ("Success"),
        ERROR ("Error"),
        TIMEOUT ("Timeout"),
        INTERRUPTED("Interrupted"),
        UNKNOWN ("Unknown");

        Type(String description) {
            this.description = description;
        }

        private final String description;

        public String getDescription() {
            return description;
        }
    }



    private final Type type;

    private final Duration computationTime;

    private final String successfulTactic;

    private final Exception exception;

    private IsabelleResult(Type type, Duration computationTime, String successfulTactic, Exception exception) {
        this.type = type;
        this.computationTime = computationTime;
        this.successfulTactic = successfulTactic;
        this.exception = exception;
    }

    public boolean isSuccessful() {
        return type == Type.SUCCESS;
    }

    public static IsabelleResult getTimeoutResult(Duration computationTime) {
        return new IsabelleResult(Type.TIMEOUT, computationTime, null, null);
    }

    public static IsabelleResult getErrorResult(Exception exception) {
        return new IsabelleResult(Type.ERROR, null, null, exception);
    }

    public static IsabelleResult getSuccessResult(String successfulTactic, Duration computationTime) {
        return new IsabelleResult(Type.SUCCESS, computationTime, successfulTactic, null);
    }

    public static IsabelleResult getInterruptedResult() {
        return new IsabelleResult(Type.INTERRUPTED, null, null, null);
    }

    public static IsabelleResult getUnknownResult() {
        return new IsabelleResult(Type.UNKNOWN, null, null, null);
    }

    public boolean isError() {
        return type == Type.ERROR;
    }

    public boolean isTimeout() {
        return type == Type.TIMEOUT;
    }

    public Duration getComputationTime() {
        return this.computationTime;
    }

    public Exception getException() {
        return this.exception;
    }

    public String getSuccessfulTactic() {
        return this.successfulTactic;
    }
}
