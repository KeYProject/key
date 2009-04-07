package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.Z3Solver;

public class TestZ3 extends TestSMTSolver {

    private static boolean z3NotInstalled = false;

    @Override
    public SMTSolver getSolver() {
	return new Z3Solver();
    }

    @Override
    protected boolean toolNotInstalled() {
	return z3NotInstalled;
    }

    @Override
    protected void setToolNotInstalled(boolean b) {
	z3NotInstalled = b;
    }
}
