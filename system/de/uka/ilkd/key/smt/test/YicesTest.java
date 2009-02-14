package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.smt.SmtSolver;
import de.uka.ilkd.key.smt.YicesSmtSolver;

public class YicesTest extends AbstractSolverTest {

    @Override
    public SmtSolver getSolver() {
	return new YicesSmtSolver();
    }

}
