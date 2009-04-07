package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.YicesSolver;

public class TestYices extends TestSMTSolver {

    private static boolean yicesNotInstalled = false;

    @Override
    public SMTSolver getSolver() {
	return new YicesSolver();
    }

    @Override
    protected boolean toolNotInstalled() {
	return yicesNotInstalled;
    }

    @Override
    protected void setToolNotInstalled(boolean b) {
	yicesNotInstalled = b;
    }
}
