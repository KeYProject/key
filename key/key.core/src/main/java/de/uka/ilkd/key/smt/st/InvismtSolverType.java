package de.uka.ilkd.key.smt.st;

/**
 * @author Alexander Weigl
 * @version 1 (9/29/21)
 */
public class InvismtSolverType extends Z3SolverType {
    @Override
    public String getName() {
        return "INVISMT";
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
    public String getVersionParameter() {
        return "--version";
    }

    @Override
    public String[] getSupportedVersions() {
        return new String[]{"1.0"};
    }
}
