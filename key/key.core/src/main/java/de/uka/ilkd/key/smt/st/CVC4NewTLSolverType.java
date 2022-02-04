package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.communication.AbstractSolverSocket;
import de.uka.ilkd.key.smt.communication.CVC4Socket;
import de.uka.ilkd.key.smt.newsmt2.ModularSMTLib2Translator;

import javax.annotation.Nonnull;

/**
 * @author Alexander Weigl
 * @version 1 (9/29/21)
 */
public class CVC4NewTLSolverType extends AbstractSolverType {

    // TODO move to AbstractSolverType?
    @Override
    public SMTSolver createSolver(SMTProblem problem,
                                  SolverListener listener, Services services) {
        return new SMTSolverImplementation(problem, listener,
                services, this);
    }

    @Override
    public String getName() {
        return "CVC4";
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
        return new ModularSMTLib2Translator();
    }

    @Override
    public String[] getDelimiters() {
        return new String[]{"CVC4>"};
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
        return new String[]{"version 1.3", "version 1.7", "version 1.8"};
    }

    @Override
    public @Nonnull AbstractSolverSocket getSocket(ModelExtractor query) {
        return new CVC4Socket(getName(), query);
    }
}
