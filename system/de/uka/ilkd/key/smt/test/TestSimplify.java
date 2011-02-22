package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverType;


//
//public class TestSimplify extends TestSMTSolver {
//
//    private static boolean simplifyNotInstalled = false;
//
//    boolean firstTime = true;
//    
//    public TestSimplify(){
////	if(firstTime){
////	    profile = new JUnitTestProfile();
////	    initializer = new ProblemInitializer(profile);
////	    
////	    System.gc();
////	    firstTime = false;
////	}
//    }
//
//    @Override
//    public SMTRule getSolver() {
//	return new SMTRule(new Name("TEST_SIMPLIFY"),SolverType.SIMPLIFY_SOLVER);
//    }
//
//    @Override
//    protected boolean toolNotInstalledChecked() {
//	return simplifyNotInstalled;
//    }
//
//    @Override
//    protected void setToolNotInstalledChecked(boolean b) {
//	simplifyNotInstalled = b;
//    }
//}
