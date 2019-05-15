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

package de.uka.ilkd.key.smt.test;


import de.uka.ilkd.key.smt.SolverType;

public class TestCvc3 extends TestSMTSolver {
    private static final String SYSTEM_PROPERTY_SOLVER_PATH = "cvc3SolverPath";

    private static boolean isInstalled = false;
    private static boolean installChecked = false;
    
    
    @Override
    public boolean toolNotInstalled() {
	if (!installChecked) {    
	    isInstalled = getSolverType().isInstalled(true);
	    installChecked = true;
	    if(!isInstalled) {
	    	System.out.println("Warning: " + getSolverType().getName() + " is not installed, tests skipped.");
	      System.out.println("Maybe use JVM system property \"" + SYSTEM_PROPERTY_SOLVER_PATH + "\" to define the path to the CVC3 command.");
	    }	  
		if(isInstalled &&!getSolverType().supportHasBeenChecked()){
			if(!getSolverType().checkForSupport()){
				System.out.println("Warning: " + "The version of the solver "+ getSolverType().getName() + " used for the following tests may not be supported.");
			}    			
		}
	}
	

    return !isInstalled;
    }
    
    @Override
    public SolverType getSolverType() {
       SolverType type = SolverType.CVC3_SOLVER;
       String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
       if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
          type.setSolverCommand(solverPathProperty);
       }
       return type;
    }
}