/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.SMTSolverResult;

public class CVC4Socket extends AbstractSolverSocket {

    public CVC4Socket(String name, ModelExtractor query) {
        super(name, query);
    }

    @Override
    public void messageIncoming(@Nonnull Pipe pipe, @Nonnull String msg) throws IOException {
        SolverCommunication sc = pipe.getSolverCommunication();
        if ("".equals(msg.trim())) {
            return;
        }

        // used only to steer the interaction with the solver and thus filtered out currently
        if (!msg.contains("success")) {
            sc.addMessage(msg, SolverCommunication.MessageType.OUTPUT);
        }

        if (msg.contains("error") || msg.contains("Error")) {
            sc.addMessage(msg, SolverCommunication.MessageType.ERROR);
            throw new IOException("Error while executing " + getName() + ": " + msg);
        }

        // Currently we rely on the solver to terminate after receiving "(exit)". If this does
        // not work in future, it may be that we have to forcibly close the pipe.
        if (sc.getState() == WAIT_FOR_RESULT) {
            msg = msg.trim();
            if (msg.equals("unsat")) {
                sc.setFinalResult(SMTSolverResult.createValidResult(getName()));
                sc.setState(FINISH);
                pipe.sendMessage("(exit)");
                // pipe.close();
            } else if (msg.equals("sat")) {
                sc.setFinalResult(SMTSolverResult.createInvalidResult(getName()));
                sc.setState(FINISH);
                pipe.sendMessage("(exit)");
                // pipe.close();
            } else if (msg.equals("unknown")) {
                sc.setFinalResult(SMTSolverResult.createUnknownResult(getName()));
                sc.setState(FINISH);
                pipe.sendMessage("(exit)");
                // pipe.close();
            }
        }
    }

    @Override
    public AbstractSolverSocket copy() {
        return new CVC4Socket(getName(), getQuery());
    }

}
