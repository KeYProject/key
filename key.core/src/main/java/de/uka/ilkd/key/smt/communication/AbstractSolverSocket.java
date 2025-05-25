/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

import org.jspecify.annotations.NonNull;

/**
 * The SolverSocket class describes the communication between the KeY and the SMT solver process.
 * This description is no longer part of the SolverType because in the case when we search for
 * counterexamples and one is found, the model has to be queried. This query depends on the SMT
 * problem and is not the same for all solvers of a given type.
 *
 * @author mihai
 * @author Wolfram Pfeifer (overhaul, removed legacy solvers)
 */
public abstract class AbstractSolverSocket {

    /** Indicates that the solver has not yet sent a sat/unsat/unknown result. */
    protected static final int WAIT_FOR_RESULT = 0;

    /** Indicates that the socket waits for more details (a model or a proof). */
    protected static final int WAIT_FOR_DETAILS = 1;

    /** Indicates that the socket waits for the result to a query (used by CE generator). */
    protected static final int WAIT_FOR_QUERY = 2;

    /**
     * Indicates that the socket waits for a model to be produced by the solver. This is a special
     * version of WAIT_FOR_DETAILS only used by the CE generator.
     */
    protected static final int WAIT_FOR_MODEL = 3;

    /** Indicates that the solver already sent a sat/unsat/unknown result. */
    protected static final int FINISH = 4;

    /** The name of the solver related to the socket. */
    protected final SolverType solverType;

    protected AbstractSolverSocket(SolverType solverType) {
        this.solverType = solverType;
    }

    protected String getName() {
        return solverType.getName();
    }

    /**
     * Invoked when the solver has sent a new message to its stdout or stderr.
     *
     * @param pipe the Pipe that received the message
     * @param msg the message as String
     * @throws IOException if an I/O error occurs
     */
    public SMTSolverResult.ThreeValuedTruth messageIncoming(@NonNull Pipe pipe, @NonNull String msg)
            throws IOException {
        SolverCommunication sc = pipe.getSolverCommunication();
        if (msg.isBlank() || isFilteredMessage(msg)) {
            return null;
        }

        sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);

        if (isWarningMessage(msg)) {
            handleWarningMessage(pipe, msg);
            return null;
        }

        if (isErrorMessage(msg)) {
            handleErrorMessage(pipe, msg);
        }

        if (pipe.getSolverCommunication().getState() == WAIT_FOR_RESULT) {
            return handleResultMessage(pipe, msg);
        }
        return null;
    }

    protected abstract boolean isValidResultMessage(@NonNull String msg);

    protected abstract boolean isFalsifiableResultMessage(@NonNull String msg);

    protected abstract boolean isUnknownResultMessage(@NonNull String msg);

    protected abstract boolean isFilteredMessage(String msg);

    protected abstract boolean isErrorMessage(String msg);

    protected abstract boolean isWarningMessage(String msg);



    protected abstract void sendValidResultMessages(Pipe pipe) throws IOException;

    protected abstract void sendFalsifiableResultMessages(Pipe pipe) throws IOException;

    protected abstract void sendUnknownResultMessages(Pipe pipe) throws IOException;

    protected abstract void sendExitMessages(Pipe pipe) throws IOException;

    protected void handleWarningMessage(@NonNull Pipe pipe, @NonNull String msg)
            throws IOException {
        pipe.getSolverCommunication().addMessage(msg, SolverCommunication.MessageType.ERROR);
    }

    protected void handleErrorMessage(@NonNull Pipe pipe, @NonNull String msg) throws IOException {
        pipe.getSolverCommunication().addMessage(msg, SolverCommunication.MessageType.ERROR);
        throw new IOException(getName() + " encountered an error: " + msg);
    }

    protected SMTSolverResult.ThreeValuedTruth handleResultMessage(@NonNull Pipe pipe,
            @NonNull String msg) throws IOException {
        if (isValidResultMessage(msg)) {
            return handleValidResultMessage(pipe, msg);
        } else if (isFalsifiableResultMessage(msg)) {
            return handleFalsifiableResultMessage(pipe, msg);
        } else if (isUnknownResultMessage(msg)) {
            return handleUnknownResultMessage(pipe, msg);
        }
        throw new IllegalStateException(
            getName() + " encountered an error when parsing message: " + msg);
    }

    protected SMTSolverResult.ThreeValuedTruth handleValidResultMessage(@NonNull Pipe pipe,
            @NonNull String msg) throws IOException {
        if (isValidResultMessage(msg)) {
            pipe.getSolverCommunication().setState(FINISH);
            sendValidResultMessages(pipe);
            return SMTSolverResult.ThreeValuedTruth.VALID;
        }
        throw new IllegalStateException(
            getName() + " encountered an error when parsing message: " + msg);
    }

    protected SMTSolverResult.ThreeValuedTruth handleFalsifiableResultMessage(@NonNull Pipe pipe,
            @NonNull String msg) throws IOException {
        if (isFalsifiableResultMessage(msg)) {
            pipe.getSolverCommunication().setState(FINISH);
            sendFalsifiableResultMessages(pipe);
            return SMTSolverResult.ThreeValuedTruth.FALSIFIABLE;
        }
        throw new IllegalStateException(
            getName() + " encountered an error when parsing message: " + msg);
    }

    protected SMTSolverResult.ThreeValuedTruth handleUnknownResultMessage(@NonNull Pipe pipe,
            @NonNull String msg) throws IOException {
        if (isUnknownResultMessage(msg)) {
            pipe.getSolverCommunication().setState(FINISH);
            sendUnknownResultMessages(pipe);
            return SMTSolverResult.ThreeValuedTruth.UNKNOWN;
        }
        throw new IllegalStateException(
            getName() + " encountered an error when parsing message: " + msg);
    }

    /**
     * Modify an SMT problem String in some way (e.g. prepend some SMT commands). By default, the
     * String is not changed at all.
     *
     * @param problem the SMT problem String to be modified
     * @return a modified version of the problem
     */
    public String modifyProblem(String problem) {
        return problem;
    }

    /**
     * Creates a new solver socket that can handle the communication for the given solver type.
     *
     * @param type the SolverType to create the socket for
     * @param query the ModelExtractor that can be used to extract a counterexample (for non-CE
     *        solvers this can be null)
     * @return the newly created socket
     */
    public static @NonNull AbstractSolverSocket createSocket(@NonNull SolverType type,
            ModelExtractor query) {
        return type.getSocket(query);
    }

    /**
     * @return a shallow copy of the socket at hand (new object with the same class and identical
     *         attributes)
     */
    public abstract AbstractSolverSocket copy();
}
