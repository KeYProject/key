package de.uka.ilkd.key.smt.test;


import de.uka.ilkd.key.smt.SolverType;



public class TestSimplify extends TestSMTSolver {

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
	return SolverType.SIMPLIFY_SOLVER;
    }


}
