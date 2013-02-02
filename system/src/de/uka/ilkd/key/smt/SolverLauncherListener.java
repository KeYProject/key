// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.smt;

import java.util.Collection;

/**
 * This interface can be used to observe a launcher.
 * */
public interface SolverLauncherListener {
	
    public void launcherStopped(SolverLauncher launcher,
	    Collection<SMTSolver> problemSolvers);

    public void launcherStarted(Collection<SMTProblem> problems,
	    Collection<SolverType> solverTypes, SolverLauncher launcher);
}
