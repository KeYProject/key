package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SimplifySolver;
import de.uka.ilkd.key.smt.SmtSolver;



public class SimplifyTest extends AbstractSolverTest {

    public SmtSolver getSolver() {
	return new SimplifySolver();
    }
    
    
}
