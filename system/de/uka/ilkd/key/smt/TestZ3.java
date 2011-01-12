package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.Z3Solver;

public class TestZ3 extends TestSMTSolver {

    private static boolean z3NotInstalled = false;
    private SMTSolver z3 = new Z3Solver();

    @Override
    public SMTRule getSolver() {
	
	return new SMTRule(new Name("TEST_Z3"),z3);
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
