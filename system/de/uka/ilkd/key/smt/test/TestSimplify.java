package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SimplifySolver;
import de.uka.ilkd.key.smt.SMTSolver;



public class TestSimplify extends TestSMTSolver {

    private static boolean simplifyNotInstalled = false;

    @Override
    public SMTSolver getSolver() {
	return new SimplifySolver();
    }

    @Override
    protected boolean toolNotInstalledChecked() {
	return simplifyNotInstalled;
    }

    @Override
    protected void setToolNotInstalledChecked(boolean b) {
	simplifyNotInstalled = b;
    }
}
