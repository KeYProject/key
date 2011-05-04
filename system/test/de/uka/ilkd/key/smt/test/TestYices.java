// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SolverType;


public class TestYices extends TestSMTSolver {

    private static boolean isInstalled = false;
    private static boolean installChecked = false;
    
    
    @Override
    public boolean toolNotInstalled() {
	if (!installChecked) {    
	    isInstalled = getSolverType().isInstalled(true);
	    installChecked = true;
	    if(!isInstalled) {
		System.out.println("Warning: " + getSolverType().getName() + " is not installed, tests skipped.");
	    }	    
	}
	
        return false;
    }

    @Override
    public SolverType getSolverType() {
	return SolverType.YICES_SOLVER;
    }


}
