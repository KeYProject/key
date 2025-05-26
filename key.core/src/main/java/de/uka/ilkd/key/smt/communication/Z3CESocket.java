/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.communication;

import java.io.IOException;

import de.uka.ilkd.key.smt.ModelExtractor;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

import org.jspecify.annotations.NonNull;

public class Z3CESocket extends AbstractCESolverSocket {

    public Z3CESocket(SolverType solverType, ModelExtractor query) {
        super(solverType, query);
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
        return msg.equals("success");
    }

    @Override
    protected boolean isErrorMessage(String msg) {
        return msg.startsWith("(error") && !msg.contains("WARNING:");
    }

    @Override
    protected boolean isWarningMessage(String msg) {
        return msg.startsWith("(error") && msg.contains("WARNING:");
    }

    @Override
    protected void sendValidResultMessages(Pipe pipe) throws IOException {
        // TODO: proof production is currently completely disabled, since it does not work
        // with the legacy Z3 translation (proof-production not enabled) and also not
        // really needed
        // pipe.sendMessage("(get-proof)");
        pipe.sendMessage("(get-unsat-core)");
        pipe.sendMessage("(exit)");
    }

    @Override
    protected void sendFalsifiableResultMessages(Pipe pipe) throws IOException {
    }

    @Override
    protected void sendUnknownResultMessages(Pipe pipe) throws IOException {
        pipe.sendMessage("(exit)\n");
    }

    @Override
    protected boolean isModelMessage(String msg) {
        return msg.equals("endmodel");
    }

    @Override
    protected void sendModelRequestMessages(Pipe pipe) throws IOException {
        pipe.sendMessage("(get-model)");
        pipe.sendMessage("(echo \"endmodel\")");
    }

    @Override
    protected void sendExitMessages(Pipe pipe) throws IOException {
        pipe.sendMessage("(exit)\n");
    }

    @Override
    public AbstractSolverSocket copy() {
        return new Z3CESocket(solverType, getQuery());
    }

}
