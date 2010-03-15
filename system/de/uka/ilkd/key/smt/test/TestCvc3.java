package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.smt.CVC3Solver;
import de.uka.ilkd.key.smt.SMTRuleNew;
import de.uka.ilkd.key.smt.SMTSolver;

public class TestCvc3 extends TestSMTSolver {

    private static boolean cvc3NotInstalled = false;
    private SMTSolver cvc3 = new CVC3Solver();

    @Override
    public SMTRuleNew getSolver() {
	return new SMTRuleNew(new Name("TEST_CVC3"),cvc3);
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
