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
import de.uka.ilkd.key.smt.SimplifySolver;



public class TestSimplify extends TestSMTSolver {

    private static boolean simplifyNotInstalled = false;
    private SMTSolver simplify = new SimplifySolver();
    boolean firstTime = true;
    
    public TestSimplify(){
//	if(firstTime){
//	    profile = new JUnitTestProfile();
//	    initializer = new ProblemInitializer(profile);
//	    
//	    System.gc();
//	    firstTime = false;
//	}
    }

    @Override
    public SMTRule getSolver() {
	return new SMTRule(new Name("TEST_SIMPLIFY"),simplify);
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
