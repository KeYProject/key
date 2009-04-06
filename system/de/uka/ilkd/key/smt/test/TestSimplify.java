package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SimplifySolver;
import de.uka.ilkd.key.smt.SMTSolver;



public class TestSimplify extends TestSMTSolver {

    public SMTSolver getSolver() {
	return new SimplifySolver();
    }
    
    
}
