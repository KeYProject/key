/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;

public class Z3Socket extends AbstractSolverSocket {

    public Z3Socket(String name, ModelExtractor query) {
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

        // used only to steer the interaction with the solver and thus filtered out currently
        if (!msg.equals("success")) {
            sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
        }

        switch (sc.getState()) {
        case WAIT_FOR_RESULT:
            if (msg.equals("unsat")) {
                sc.setFinalResult(SMTSolverResult.createValidResult(getName()));
                // TODO: proof production is currently completely disabled, since it does not work
                // with the legacy Z3 translation (proof-production not enabled) and also not
                // really needed
                // pipe.sendMessage("(get-proof)");
                pipe.sendMessage("(get-unsat-core)");
                pipe.sendMessage("(exit)");
                sc.setState(WAIT_FOR_DETAILS);
            }
            if (msg.equals("sat")) {
                sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
                pipe.sendMessage("(get-model)");
                pipe.sendMessage("(exit)");
                sc.setState(WAIT_FOR_DETAILS);

            }
            if (msg.equals("unknown")) {
                sc.setFinalResult(SMTSolverResult.createUnknownResult(getName()));
                pipe.sendMessage("(exit)\n");
                sc.setState(WAIT_FOR_DETAILS);
            }
            break;

        case WAIT_FOR_DETAILS:
            // Currently we rely on the solver to terminate after receiving "(exit)". If this does
            // not work in future, it may be that we have to forcibly close the pipe.
            // if (msg.equals("success")) {
            // pipe.sendMessage("(exit)");
            // pipe.close();
            // }
            break;
        }
    }

    @Override
    public AbstractSolverSocket copy() {
        return new Z3Socket(getName(), getQuery());
    }

}
