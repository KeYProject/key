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