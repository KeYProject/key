package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SimplifySolver;
import de.uka.ilkd.key.smt.SMTSolver;



public class SimplifyTest extends AbstractSolverTest {

    public SMTSolver getSolver() {
	return new SimplifySolver();
    }
    
    
}
