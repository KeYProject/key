/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;

public class Z3CESocket extends AbstractSolverSocket {

    public Z3CESocket(String name, ModelExtractor query) {
        super(name, query);
    }

    @Override
    public void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg) throws IOException {
        SolverCommunication sc = pipe.getSolverCommunication();

        if (msg.startsWith("(error")) {
            sc.addMessage(msg, SolverCommunication.MessageType.ERROR);
            if (msg.contains("WARNING:")) {
                return;
            }
            throw new IOException("Error while executing " + getName() + ": " + msg);
        }
        // These two messages are only used to steer the interaction with the solver and are thus
        // currently filtered out to avoid cluttering up the output.
        if (!msg.equals("success") && !msg.equals("endmodel")) {
            sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
        }

        switch (sc.getState()) {
        case WAIT_FOR_RESULT:
            if (msg.equals("unsat")) {
                sc.setFinalResult(SMTSolverResult.createValidResult(getName()));
                pipe.sendMessage("(exit)");
                sc.setState(WAIT_FOR_DETAILS);
            }
            if (msg.equals("sat")) {
                sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
                pipe.sendMessage("(get-model)");
                pipe.sendMessage("(echo \"endmodel\")");
                sc.setState(WAIT_FOR_MODEL);
            }
            if (msg.equals("unknown")) {
                sc.setFinalResult(SMTSolverResult.createUnknownResult(getName()));
                sc.setState(WAIT_FOR_DETAILS);
                pipe.sendMessage("(exit)");
            }

            break;

        case WAIT_FOR_DETAILS:
            // Currently we rely on the solver to terminate after receiving "(exit)". If this does
            // not work in future, it may be that we have to forcibly close the pipe.
            break;

        case WAIT_FOR_QUERY:
            if (!msg.equals("success")) {
                getQuery().messageIncoming(pipe, msg);
            }
            break;

        case WAIT_FOR_MODEL:
            if (msg.equals("endmodel")) {
                if (getQuery() != null && getQuery().getState() == ModelExtractor.DEFAULT) {
                    getQuery().getModel().setEmpty(false);
                    getQuery().start(pipe);
                    sc.setState(WAIT_FOR_QUERY);
                } else {
                    pipe.sendMessage("(exit)\n");
                    sc.setState(WAIT_FOR_DETAILS);
                }
            }
            break;
        default:
            throw new IllegalStateException("Unexpected value: " + sc.getState());
        }
    }

    @Override
    public AbstractSolverSocket copy() {
        return new Z3CESocket(getName(), getQuery());
    }

}
