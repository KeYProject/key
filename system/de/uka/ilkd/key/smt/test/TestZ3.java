package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverType;


public class TestZ3 extends TestSMTSolver {

    private static boolean z3NotInstalled = false;

    @Override
    public SMTRule getSolver() {
	
	return new SMTRule(new Name("TEST_Z3"),SolverType.Z3_SOLVER);
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
