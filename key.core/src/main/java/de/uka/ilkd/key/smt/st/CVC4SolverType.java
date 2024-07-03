/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.smt.st;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.communication.CVC4Socket;

/**
 * @author Alexander Weigl
 * @version 1 (9/29/21)
 */
public class CVC4SolverType extends AbstractSolverType {

    // TODO move to AbstractSolverType?
    @Override
    public SMTSolver createSolver(SMTProblem problem,
            SolverListener listener, Services services) {
        return new SMTSolverImplementation(problem, listener,
            services, this);
    }

    @Override
    public String getName() {
        return "CVC4 (Legacy Translation)";
    }

    @Override
    public String getInfo() {
        // todo Auto-generated method stub
        return null;
    }

    @Override
    public String getDefaultSolverParameters() {
        return "--no-print-success -m --interactive --lang smt2";
    }

    @Override
    public String getDefaultSolverCommand() {
        return "cvc4";
    }

    @Override
    public SMTTranslator createTranslator(Services services) {
        final AbstractSMTTranslator.Configuration conf =
            new AbstractSMTTranslator.Configuration(false, true);
        return new SmtLib2Translator(services, conf);
    }

    @Override
    public String[] getDelimiters() {
        return new String[] { "CVC4>" };
    }

    @Override
    public boolean supportsIfThenElse() {
        return true;
    }

    @Override
    public String getVersionParameter() {
        return "--version";
    }

    @Override
    public String[] getSupportedVersions() {
        return new String[] { "version 1.3" };
    }

    @Override
    public @Nonnull AbstractSolverSocket getSocket(ModelExtractor query) {
        return new CVC4Socket(getName(), query);
    }

}
