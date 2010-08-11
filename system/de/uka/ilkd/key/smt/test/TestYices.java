// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.smt.test;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.YicesSolver;

public class TestYices extends TestSMTSolver {

    private static boolean yicesNotInstalled = false;
    private SMTSolver yices = new YicesSolver();

    @Override
    public SMTRule getSolver() {
	return new SMTRule(new Name("TEST_YICES"),yices);
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
