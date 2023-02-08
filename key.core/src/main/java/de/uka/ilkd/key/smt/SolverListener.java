package de.uka.ilkd.key.smt;

public interface SolverListener {
    void processStarted(SMTSolver solver, SMTProblem problem);

    void processInterrupted(SMTSolver solver, SMTProblem problem, Throwable e);

    void processStopped(SMTSolver solver, SMTProblem problem);

    void processTimeout(SMTSolver solver, SMTProblem problem);

    void processUser(SMTSolver solver, SMTProblem problem);
}
