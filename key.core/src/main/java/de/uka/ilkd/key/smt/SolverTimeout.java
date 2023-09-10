/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
