/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.smt;

import java.util.TimerTask;

import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;

/**
 * The class controls the timer that checks for a solver whether it exceeds a pre-defined timeout.
 */
@SuppressWarnings("auxiliaryclass") // Session is an auxiliary class in SolverLauncher.java
class SolverTimeout extends TimerTask {
    private final SMTSolver solver;
    private final Object session;

    public SolverTimeout(SMTSolver solver, Object session) {
        this.solver = solver;
        this.session = session;
    }

    @Override
    public void run() {
        if (session != null) {
            // The only caller (SolverLauncher.fillRunningList) always passes a Session.
            ((Session) session).interruptSolver(solver, ReasonOfInterruption.Timeout);
        } else {
            solver.interrupt(ReasonOfInterruption.Timeout);
        }
    }
}
