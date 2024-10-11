/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation.automation;

import java.time.Duration;
import java.time.Instant;
import java.util.concurrent.Callable;

/**
 * An Isabelle solver. May use different methods to arrive at the result.
 * Implements callable. Thread management must be handled by callers.
 */
public interface IsabelleSolver extends Callable<IsabelleResult> {
    /**
     * UI component index
     *
     * @return the index corresponding to this solver
     */
    int getSolverIndex();

    /**
     * state of the solver
     */
    enum SolverState {
        Waiting, Preparing, Parsing, Running, Stopped
    }

    /**
     * Name for the solver instance
     *
     * @return name of the solver instance
     */
    String name();

    /**
     * Getter for the problem this solver will work on
     *
     * @return The problem this solver will work on
     */
    IsabelleProblem getProblem();

    /**
     * Returns the Exception encountered during proof search
     *
     * @return exception encountered during proof search, if any was encountered.
     */
    Throwable getException();

    /**
     * aborts processing
     */
    void abort();

    /**
     * Getter for start time of the solver
     *
     * @return Time solver started computing (after preparation)
     */
    Instant getStartTime();

    /**
     * Getter for computation time
     *
     * @return computation time before solver stopped
     */
    Duration getComputationTime();

    /**
     * Returns the timeout time for solver in seconds
     *
     * @return timeout time for solver
     */
    int getTimeout();

    /**
     * Sets the timeout value for this solver (in seconds)
     *
     * @param timeout timeout in seconds (negative values may cause unexpected behavior)
     */
    void setTimeout(int timeout);

    /**
     * Getter for current solver state
     *
     * @return current solver state
     */
    SolverState getState();

    /**
     * Raw output of solver
     *
     * @return raw output of solver
     */
    String getRawSolverOutput();

    /**
     * Raw string of translation theory (not preamble)
     *
     * @return raw input of solver
     */
    String getRawSolverInput();

    /**
     * The final result of solver. Recommended to be null, prior to solver completion.
     *
     * @return final result of solver
     */
    IsabelleResult getFinalResult();
}
