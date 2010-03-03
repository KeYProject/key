package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.YicesSolver;

public class TestYices extends TestSMTSolver {

    private static boolean yicesNotInstalled = false;
    private SMTSolver yices = new YicesSolver();

    @Override
    public SMTSolver getSolver() {
	return yices;
    }

    @Override
    protected boolean toolNotInstalledChecked() {
	return yicesNotInstalled;
    }

    @Override
    protected void setToolNotInstalledChecked(boolean b) {
	yicesNotInstalled = b;
    }
}
