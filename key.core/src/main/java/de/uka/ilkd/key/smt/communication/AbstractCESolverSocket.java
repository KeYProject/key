/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

import org.jspecify.annotations.NonNull;

public abstract class AbstractCESolverSocket extends AbstractSolverSocket {
    private ModelExtractor query;

    /**
     * Creates a new solver socket with given solver name and ModelExtractor.
     *
     * @param solverType
     * @param query the ModelExtractor used to extract a counterexample
     */
    protected AbstractCESolverSocket(SolverType solverType, ModelExtractor query) {
        super(solverType);
        this.query = query;
    }

    @Override
    public SMTSolverResult.ThreeValuedTruth messageIncoming(@NonNull Pipe pipe, @NonNull String msg) throws IOException {
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

        return handleResultMessage(pipe, msg);
    }

    @Override
    protected SMTSolverResult.ThreeValuedTruth handleFalsifiableResultMessage(@NonNull Pipe pipe,
            @NonNull String msg) throws IOException {
        if (isFalsifiableResultMessage(msg)) {
            pipe.getSolverCommunication().setState(WAIT_FOR_MODEL);
            sendModelRequestMessages(pipe);
            return null;
        }
        throw new IllegalStateException(
            getName() + " encountered an error when parsing message: " + msg);
    }

    @Override
    protected SMTSolverResult.ThreeValuedTruth handleResultMessage(@NonNull Pipe pipe,
            @NonNull String msg) throws IOException {
        SolverCommunication sc = pipe.getSolverCommunication();
        switch (sc.getState()) {
        case WAIT_FOR_RESULT -> {
            if (isFalsifiableResultMessage(msg)) {
                return handleFalsifiableResultMessage(pipe, msg);
            }
            return super.handleResultMessage(pipe, msg);
        }
        case WAIT_FOR_DETAILS -> {
            return null;
        }
        // Currently we rely on the solver to terminate after receiving "(exit)". If this does
        // not work in future, it may be that we have to forcibly close the pipe.
        case WAIT_FOR_QUERY -> {
            if (!isFilteredMessage(msg)) {
                getQuery().messageIncoming(pipe, msg);
                if (getQuery().getState() == ModelExtractor.FINISHED) {
                    return SMTSolverResult.ThreeValuedTruth.FALSIFIABLE;
                }
            }
            return null;
        }
        case WAIT_FOR_MODEL -> {
            if (isModelMessage(msg)) {
                if (getQuery() != null && getQuery().getState() == ModelExtractor.DEFAULT) {
                    getQuery().getModel().setEmpty(false);
                    getQuery().start(pipe);
                    sc.setState(WAIT_FOR_QUERY);
                } else {
                    sendExitMessages(pipe);
                    return SMTSolverResult.ThreeValuedTruth.FALSIFIABLE;
                }
            }
            return null;
        }
        default -> throw new IllegalStateException("Unexpected value: " + sc.getState());
        }
    }

    protected abstract boolean isModelMessage(String msg);

    protected abstract void sendModelRequestMessages(Pipe pipe) throws IOException;

    public ModelExtractor getQuery() {
        return query;
    }

    public void setQuery(ModelExtractor query) {
        this.query = query;
    }
}
