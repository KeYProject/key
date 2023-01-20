package de.uka.ilkd.key.smt;

import java.util.TimerTask;

import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;

/**
 * The class controls the timer that checks for a solver whether it exceeds a pre-defined timeout.
 */
class SolverTimeout extends TimerTask {
    private final SMTSolver solver;
    private final Session session;

    public SolverTimeout(SMTSolver solver, Session session) {
        this.solver = solver;
        this.session = session;
    }

    @Override
    public void run() {
        if (session != null) {
            session.interruptSolver(solver, ReasonOfInterruption.Timeout);
        } else {
            solver.interrupt(ReasonOfInterruption.Timeout);
        }
    }
}
