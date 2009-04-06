package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.Z3Solver;

public class TestZ3 extends TestSMTSolver {

    @Override
    public SMTSolver getSolver() {
	return new Z3Solver();
    }

}
