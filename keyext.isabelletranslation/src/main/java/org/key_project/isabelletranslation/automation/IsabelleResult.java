/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import java.time.Duration;

/**
 * This class stores the result of a {@link IsabelleSolver}.
 * This includes computation times and in some cases successful tactics and exceptions.
 */
public class IsabelleResult {
    /**
     * Returns a {@link String} description of the type of this result.
     *
     * @return description of the type of result this is
     */
    public String getDescription() {
        return this.type.getDescription();
    }

    /**
     * Returns the type of result this is
     *
     * @return the type of result this is
     */
    public Type getType() {
        return this.type;
    }

    /**
     * Enum containing different types of Results.
     */
    public enum Type {
        /**
         * Successful result. (Proof found)
         */
        SUCCESS("Success"),
        /**
         * Error result. (Encountered exception)
         */
        ERROR("Error"),
        /**
         * Timeout result. (No proof found in time)
         */
        TIMEOUT("Timeout"),
        /**
         * Interrupt result. (Interrupt during proof search)
         */
        INTERRUPTED("Interrupted"),
        /**
         * Unknown result. (Something went wrong, but unknown what did)
         */
        UNKNOWN("Unknown");

        Type(String description) {
            this.description = description;
        }

        private final String description;

        /**
         * Returns a {@link String} description of the result type.
         *
         * @return a {@link String} description of the result type.
         */
        public String getDescription() {
            return description;
        }
    }

    /**
     * The type of this result
     */
    private final Type type;

    /**
     * The computation time for this result. Only set for successful and timeout results.
     */
    private final Duration computationTime;

    /**
     * A successful tactic returned by an Isabelle automation method
     */
    private final String successfulTactic;

    /**
     * An exception thrown during computation by the solver
     */
    private final Exception exception;

    private IsabelleResult(Type type, Duration computationTime, String successfulTactic,
            Exception exception) {
        this.type = type;
        this.computationTime = computationTime;
        this.successfulTactic = successfulTactic;
        this.exception = exception;
    }

    /**
     * Creates a timeout result.
     *
     * @param computationTime the time taken for timeout to occur
     * @return Isabelle result representing a timeout
     */
    public static IsabelleResult getTimeoutResult(Duration computationTime) {
        return new IsabelleResult(Type.TIMEOUT, computationTime, null, null);
    }

    /**
     * Returns an error result
     *
     * @param exception the exception that caused computation to fail
     * @return Isabelle result representing an error
     */
    public static IsabelleResult getErrorResult(Exception exception) {
        return new IsabelleResult(Type.ERROR, null, null, exception);
    }

    /**
     * Creates a successful result
     *
     * @param successfulTactic the successful tactic found by a solver
     * @param computationTime time taken for proof search
     * @return Isabelle result representing a success
     */
    public static IsabelleResult getSuccessResult(String successfulTactic,
            Duration computationTime) {
        return new IsabelleResult(Type.SUCCESS, computationTime, successfulTactic, null);
    }

    /**
     * Creates an interrupt result
     *
     * @return Isabelle result representing an Interrupt
     */
    public static IsabelleResult getInterruptedResult() {
        return new IsabelleResult(Type.INTERRUPTED, null, null, null);
    }

    /**
     * Creates an unknown result
     *
     * @return Isabelle result representing an unknown result
     */
    public static IsabelleResult getUnknownResult() {
        return new IsabelleResult(Type.UNKNOWN, null, null, null);
    }



    /**
     * Is this result successful?
     *
     * @return true - if successful, false - otherwise
     */
    public boolean isSuccessful() {
        return type == Type.SUCCESS;
    }

    /**
     * Is this an error result?
     *
     * @return true - if error, false - otherwise
     */
    public boolean isError() {
        return type == Type.ERROR;
    }

    /**
     * Is this a timeout result?
     *
     * @return true - if timeout, false - otherwise
     */
    public boolean isTimeout() {
        return type == Type.TIMEOUT;
    }

    public Duration getComputationTime() {
        return this.computationTime;
    }

    /**
     * Getter for exception
     *
     * @return exception encountered during proving || null if not error result
     */
    public Exception getException() {
        return this.exception;
    }

    /**
     * Successful proof tactic
     *
     * @return successful tactic || null if not successful
     */
    public String getSuccessfulTactic() {
        return this.successfulTactic;
    }

    @Override
    public String toString() {
        return getDescription();
    }
}
