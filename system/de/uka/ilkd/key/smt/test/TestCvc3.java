package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverType;

public class TestCvc3 extends TestSMTSolver {

    private static boolean cvc3NotInstalled = false;

    @Override
    public SMTRule getSolver() {
	return new SMTRule(new Name("TEST_CVC3"),SolverType.CVC3_SOLVER);
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
