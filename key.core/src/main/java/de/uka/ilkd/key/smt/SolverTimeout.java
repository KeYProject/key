/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.TimerTask;

import de.uka.ilkd.key.smt.SMTSolver.ReasonOfInterruption;
import org.jspecify.annotations.NonNull;

/**
 * The class controls the timer that checks for a solver whether it exceeds a pre-defined timeout.
 */
class SolverTimeout extends TimerTask {
    private final SMTSolver solver;

    public SolverTimeout(@NonNull SMTSolver solver) {
        this.solver = solver;
    }

    @Override
    public void run() {
        solver.interrupt(ReasonOfInterruption.Timeout);
    }
}
