package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.Z3Solver;

public class TestZ3 extends TestSMTSolver {

    private static boolean z3NotInstalled = false;
    private SMTSolver z3 = new Z3Solver();

    @Override
    public SMTSolver getSolver() {
	
	return z3;
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
