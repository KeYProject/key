package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SimplifySolver;



public class TestSimplify extends TestSMTSolver {

    private static boolean simplifyNotInstalled = false;
    private SMTSolver simplify = new SimplifySolver();
    boolean firstTime = true;
    
    public TestSimplify(){
//	if(firstTime){
//	    profile = new JUnitTestProfile();
//	    initializer = new ProblemInitializer(profile);
//	    
//	    System.gc();
//	    firstTime = false;
//	}
    }

    @Override
    public SMTSolver getSolver() {
	return simplify;
    }

    @Override
    protected boolean toolNotInstalledChecked() {
	return simplifyNotInstalled;
    }

    @Override
    protected void setToolNotInstalledChecked(boolean b) {
	simplifyNotInstalled = b;
    }
}
