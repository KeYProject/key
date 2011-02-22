package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverType;


public class TestYices extends TestSMTSolver {

    private static boolean yicesNotInstalled = false;


    @Override
    public SMTRule getSolver() {
	return new SMTRule(new Name("TEST_YICES"),SolverType.YICES_SOLVER);
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
