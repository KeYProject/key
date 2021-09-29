package de.uka.ilkd.key.smt.st;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTTranslator;
import de.uka.ilkd.key.smt.SolverListener;

/**
 * @author Alexander Weigl
 * @version 1 (9/29/21)
 */
class InvismtSolverType extends AbstractSolverType {
    @Override
    public SMTSolver createSolver(SMTProblem problem, SolverListener listener, Services services) {
        return null;
    }

    @Override
    public String getName() {
        return "InviSMT";
    }

    @Override
    public String getInfo() {
        return "Interactive SMT Solver wraps various SMT-Solvers";
    }

    @Override
    public String getDefaultSolverParameters() {
        return "";
    }

    @Override
    public String getDefaultSolverCommand() {
        return "invismt.sh";
    }

    @Override
    public SMTTranslator createTranslator(Services services) {
        return null;
    }

    @Override
    public String[] getDelimiters() {
        return new String[0];
    }

    @Override
    public boolean supportsIfThenElse() {
        return false;
    }

    @Override
    public String getVersionParameter() {
        return null;
    }

    @Override
    public String[] getSupportedVersions() {
        return new String[0];
    }
}
