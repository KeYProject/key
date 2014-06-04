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

import junit.framework.Assert;
import de.uka.ilkd.key.smt.SolverType;


public class TestZ3 extends TestSMTSolver {


    private static final String SYSTEM_PROPERTY_SOLVER_PATH = "z3SolverPath";

    private static boolean isInstalled = false;
    private static boolean installChecked = false;
    
    
    @Override
    public boolean toolNotInstalled() {
    	if (!installChecked) {    
    		isInstalled = getSolverType().isInstalled(true);
    		installChecked = true;
    		if(!isInstalled) {
    			System.out.println("Warning: " + getSolverType().getName() + " is not installed, tests skipped.");
            System.out.println("Maybe use JVM system property \"" + SYSTEM_PROPERTY_SOLVER_PATH + "\" to define the path to the Z3 command.");
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
       SolverType type = SolverType.Z3_SOLVER;
       String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
       if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
          type.setSolverCommand(solverPathProperty);
       }
       return type;
    }
    
    //These testcases are z3 specific, because other solver don't support integer division.
    public void testDiv1() {
        Assert.assertTrue(correctResult(testFile + "div1.key", true));
    }
    
    public void testDiv3() {
        Assert.assertTrue(correctResult(testFile + "div3.key", true));
    }
    
    public void testDiv5() {
        Assert.assertTrue(correctResult(testFile + "div5.key", false));
    }
    
    public void testDiv6() {
        Assert.assertTrue(correctResult(testFile + "div6.key", false));
    }
    
}
