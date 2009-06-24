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
    protected boolean toolNotInstalledChecked() {
	return z3NotInstalled;
    }

    @Override
    protected void setToolNotInstalledChecked(boolean b) {
	z3NotInstalled = b;
    }
}
