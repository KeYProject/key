package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.CVC3Solver;
import de.uka.ilkd.key.smt.SMTSolver;

public class TestCvc3 extends TestSMTSolver {

    private static boolean cvc3NotInstalled = false;
    private SMTSolver cvc3 = new CVC3Solver();

    @Override
    public SMTSolver getSolver() {
	return cvc3;
    }

    @Override
    protected boolean toolNotInstalledChecked() {
	return cvc3NotInstalled;
    }

    @Override
    protected void setToolNotInstalledChecked(boolean b) {
	cvc3NotInstalled = b;
    }
}
