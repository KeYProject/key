// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.smt.CVC3Solver;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolver;

public class TestCvc3 extends TestSMTSolver {

    private static boolean cvc3NotInstalled = false;
    private SMTSolver cvc3 = new CVC3Solver();

    @Override
    public SMTRule getSolver() {
	return new SMTRule(new Name("TEST_CVC3"),cvc3);
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
