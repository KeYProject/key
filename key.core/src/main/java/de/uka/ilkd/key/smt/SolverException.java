/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.Collection;

/**
 * Encapsulates all exceptions that have occurred while executing the solvers.
 */
public class SolverException extends RuntimeException {
    private static final long serialVersionUID = 1L;
    private final transient Collection<SMTSolver> solvers;

    public SolverException(Collection<SMTSolver> solvers) {
        super();
        this.solvers = solvers;
    }

    public Collection<SMTSolver> getSolvers() {
        return solvers;
    }

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder("\n");
        for (SMTSolver solver : solvers) {
            s.append("Solver: ").append(solver.name()).append("\n");
            if (solver.getProblem().getGoal() != null) {
                s.append("Goal-No.: ").append(solver.getProblem().getGoal().node().serialNr())
                        .append("\n");
            }
            s.append("Exception:\n");
            s.append(solver.getException());
            s.append("\n");

        }
        return s.toString();
    }
}
