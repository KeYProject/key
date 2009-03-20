package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.Z3Solver;

public class Z3Test extends AbstractSolverTest {

    @Override
    public SMTSolver getSolver() {
	return new Z3Solver();
    }

}
