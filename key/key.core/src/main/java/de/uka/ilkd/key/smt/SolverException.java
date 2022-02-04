// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt;

import java.util.Collection;

/**
 * Encapsulates all exceptions that have occurred while
 * executing the solvers.
 * */
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
	public void printStackTrace() {
		System.err.println(toString());
	}

	@Override
	public String toString() {
		StringBuilder s = new StringBuilder("\n");
		for (SMTSolver solver : solvers) {
			s.append("Solver: ").append(solver.name()).append("\n");
			if (solver.getProblem().getGoal() != null) {
				s.append("Goal-No.: ")
						.append(solver.getProblem().getGoal().node().serialNr())
						.append("\n");
			}
			s.append("Exception:\n");
			s.append(solver.getException());
			s.append("\n");

		}
		return s.toString();
	}
}