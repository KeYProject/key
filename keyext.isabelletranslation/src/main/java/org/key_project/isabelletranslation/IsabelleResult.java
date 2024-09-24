package org.key_project.isabelletranslation;

public class IsabelleResult {
    public String getDescription() {
        return this.type.getDescription();
    }

    enum Type {
        SUCCESS ("Success"),
        ERROR ("Error"),
        TIMEOUT ("Timeout");

        Type(String description) {
            this.description = description;
        }

        private final String description;

        public String getDescription() {
            return description;
        }
    }



    private final Type type;

    private final long computationTime;

    private final String successfulTactic;

    private final Exception exception;

    private IsabelleResult(Type type, long computationTime, String successfulTactic, Exception exception) {
        this.type = type;
        this.computationTime = computationTime;
        this.successfulTactic = successfulTactic;
        this.exception = exception;
    }

    public boolean isSuccessful() {
        return type == Type.SUCCESS;
    }

    public static IsabelleResult getTimeoutResult(long computationTime) {
        return new IsabelleResult(Type.TIMEOUT, computationTime, null, null);
    }

    public static IsabelleResult getErrorResult(Exception exception) {
        return new IsabelleResult(Type.ERROR, -1, null, exception);
    }

    public static IsabelleResult getSuccessResult(String successfulTactic, long computationTime) {
        return new IsabelleResult(Type.SUCCESS, computationTime, successfulTactic, null);
    }

    public boolean isError() {
        return type == Type.ERROR;
    }

    public boolean isTimeout() {
        return type == Type.TIMEOUT;
    }

    public long getComputationTime() {
        return this.computationTime;
    }

    public Exception getException() {
        return this.exception;
    }

    public String getSuccessfulTactic() {
        return this.successfulTactic;
    }
}
