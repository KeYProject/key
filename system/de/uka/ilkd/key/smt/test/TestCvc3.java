package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.CVC3Solver;
import de.uka.ilkd.key.smt.SMTSolver;

public class TestCvc3 extends TestSMTSolver {

    private static boolean cvc3NotInstalled = false;

    @Override
    public SMTSolver getSolver() {
	return new CVC3Solver();
    }

    @Override
    protected boolean toolNotInstalled() {
	return cvc3NotInstalled;
    }

    @Override
    protected void setToolNotInstalled(boolean b) {
	cvc3NotInstalled = b;
    }
}
