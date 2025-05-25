/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;

import de.uka.ilkd.key.smt.solvertypes.SolverType;

import org.jspecify.annotations.NonNull;

/**
 * Socket for CVC5 (<a href="https://cvc5.github.io/">...</a>).
 */
public class CVC5Socket extends AbstractSolverSocket {

    /**
     * Create a new CVC5Socket.
     */
    public CVC5Socket(SolverType solverType) {
        super(solverType);
    }

    @Override
    protected boolean isValidResultMessage(@NonNull String msg) {
        return msg.equals("unsat");
    }

    @Override
    protected boolean isFalsifiableResultMessage(@NonNull String msg) {
        return msg.equals("sat");
    }

    @Override
    protected boolean isUnknownResultMessage(@NonNull String msg) {
        return msg.equals("unknown");
    }

    @Override
    protected boolean isFilteredMessage(String msg) {
        return msg.contains("success");
    }

    @Override
    protected boolean isErrorMessage(String msg) {
        return msg.contains("error") || msg.contains("Error");
    }

    @Override
    protected boolean isWarningMessage(String msg) {
        return false;
    }

    @Override
    protected void sendValidResultMessages(Pipe pipe) throws IOException {
        pipe.sendMessage("(exit)");
    }

    @Override
    protected void sendFalsifiableResultMessages(Pipe pipe) throws IOException {
        pipe.sendMessage("(exit)");
    }

    @Override
    protected void sendUnknownResultMessages(Pipe pipe) throws IOException {
        pipe.sendMessage("(exit)");
    }

    @Override
    protected void sendExitMessages(Pipe pipe) throws IOException {
        pipe.sendMessage("(exit)");
    }

    @Override
    public AbstractSolverSocket copy() {
        return new CVC5Socket(solverType);
    }

}
