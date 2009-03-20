package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.YicesSolver;

public class YicesTest extends AbstractSolverTest {

    @Override
    public SMTSolver getSolver() {
	return new YicesSolver();
    }

}
