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

import de.uka.ilkd.key.smt.st.SolverType;
import de.uka.ilkd.key.smt.st.SolverTypes;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertTrue;


public class TestZ3 extends TestSMTSolver {


    public static final String SYSTEM_PROPERTY_SOLVER_PATH = "z3SolverPath";
    private static final Logger LOGGER = LoggerFactory.getLogger(TestZ3.class);


    private static boolean isInstalled = false;
    private static boolean installChecked = false;
    
    
    @Override
    public boolean toolNotInstalled() {
    	if (!installChecked) {    
    		isInstalled = getSolverType().isInstalled(true);
    		installChecked = true;
    		if(!isInstalled) {
                LOGGER.warn("Warning: {} is not installed, tests skipped.", getSolverType().getName());
                LOGGER.warn("Maybe use JVM system property \"{}\" to define the path to the Z3 command.",
                        SYSTEM_PROPERTY_SOLVER_PATH);
    		}	  
    		
    		if(isInstalled &&!getSolverType().supportHasBeenChecked()){
    			if(!getSolverType().checkForSupport()){
                    LOGGER.warn("Warning: " + "The version of the solver {} used for the " +
                            "following tests may not be supported.", getSolverType().getName());
    			}    			
    		}
    	}

    	
    	

        return !isInstalled;
    }
    
    @Override
    public SolverType getSolverType() {
       SolverType type = SolverTypes.Z3_SOLVER;
       String solverPathProperty = System.getProperty(SYSTEM_PROPERTY_SOLVER_PATH);
       if (solverPathProperty != null && !solverPathProperty.isEmpty()) {
          type.setSolverCommand(solverPathProperty);
       }
       return type;
    }
    
    //These testcases are z3 specific, because other solver don't support integer division.
    @Test
    public void testDiv1() throws Exception {
        assertTrue(correctResult(testFile + "div1.key", true));
    }
    
    @Test
    public void testDiv3() throws Exception {
        assertTrue(correctResult(testFile + "div3.key", true));
    }
    
    @Test
    public void testDiv5() throws Exception {
        assertTrue(correctResult(testFile + "div5.key", false));
    }
    
    @Test
    public void testDiv6() throws Exception {
        assertTrue(correctResult(testFile + "div6.key", false));
    }
    
}
