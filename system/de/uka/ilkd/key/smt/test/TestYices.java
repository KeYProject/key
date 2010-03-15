package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.smt.SMTRuleNew;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.YicesSolver;

public class TestYices extends TestSMTSolver {

    private static boolean yicesNotInstalled = false;
    private SMTSolver yices = new YicesSolver();

    @Override
    public SMTRuleNew getSolver() {
	return new SMTRuleNew(new Name("TEST_YICES"),yices);
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
