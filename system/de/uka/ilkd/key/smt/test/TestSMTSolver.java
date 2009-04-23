//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt.test;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.util.HelperClassForTests;
import junit.framework.Assert;
import junit.framework.TestCase;

public abstract class TestSMTSolver extends TestCase {

    private SMTSolver solver;
    
    private HelperClassForTests helper;
   
    public static final String testFile = System.getProperty("key.home")
    + File.separator + "examples"
    + File.separator + "_testcase"
    + File.separator + "smt"
    + File.separator;

    protected void setUp() {
	solver = this.getSolver();
	helper = new HelperClassForTests();
    }
    
    /**
     * returns the solver that should be tested.
     * @return the solver to be tested.
     */
    public abstract SMTSolver getSolver();

    protected abstract boolean toolNotInstalled();

    protected abstract void setToolNotInstalled(boolean b);

    
    public void testAndnot() {
	Assert.assertTrue(correctResult(testFile + "andnot.key", false));
    }
    
    public void testOrnot() {
	Assert.assertTrue(correctResult(testFile + "ornot.key", true));
    }
    
    public void testAndornot() {
	Assert.assertTrue(correctResult(testFile + "andornot.key", false));
    }
    
    public void testAndornot2() {
	Assert.assertTrue(correctResult(testFile + "andornot2.key", true));
    }
    
    public void testImply() {
	Assert.assertTrue(correctResult(testFile + "imply.key", true));
    }
    
    public void testImply2() {
	Assert.assertTrue(correctResult(testFile + "imply2.key", true));
    }
    
    public void testImply3() {
	Assert.assertTrue(correctResult(testFile + "imply3.key", false));
    }
    
    public void testEqui1() {
	Assert.assertTrue(correctResult(testFile + "equi1.key", true));
    }
    
    public void testEqui2() {
	Assert.assertTrue(correctResult(testFile + "equi2.key", false));
    }
    
    public void testAllex1() {
	Assert.assertTrue(correctResult(testFile + "allex1.key", true));
    }
    
    public void testAllex2() {
	Assert.assertTrue(correctResult(testFile + "allex2.key", false));
    }
    
    public void testAllex3() {
	Assert.assertTrue(correctResult(testFile + "allex3.key", true));
    }
    
    public void testLogicalIte1() {
	Assert.assertTrue(correctResult(testFile + "logicalite1.key", true));
    }
    
    public void testLogicalIte2() {
	Assert.assertTrue(correctResult(testFile + "logicalite2.key", false));
    }
    
    public void testTermIte1() {
	Assert.assertTrue(correctResult(testFile + "termite1.key", true));
    }
    
    public void testTermlIte2() {
	Assert.assertTrue(correctResult(testFile + "termite2.key", false));
    }
    
    public void testEqual1() {
	Assert.assertTrue(correctResult(testFile + "equal1.key", true));
    }
    
    public void testEqual2() {
	Assert.assertTrue(correctResult(testFile + "equal2.key", false));
    }
    
    public void testSubsort1() {
	Assert.assertTrue(correctResult(testFile + "subsort1.key", true));
    }
    
    public void testSubsort2() {
	Assert.assertTrue(correctResult(testFile + "subsort2.key", false));
    }
    
    public void testAdd1() {
	Assert.assertTrue(correctResult(testFile + "add1.key", true));
    }
    
    /*public void testAdd2() {
	Assert.assertTrue(correctResult(testFile + "add2.key", false));
    }*/
    
    public void testMult1() {
	Assert.assertTrue(correctResult(testFile + "mult1.key", true));
    }
    
    private boolean correctResult(String filepath, boolean isValid) {
	if (toolNotInstalled()) {
	    return true;
	}
	
	SMTSolverResult result;
	
	try {
	    result = checkFile(filepath);
	} catch (Exception e) {
	    //System.out.println();
	    System.out.println("Warning: " + this.getSolver().name() 
                               + " not found, skipped.");
	    //System.out.println();
	    //e.printStackTrace();
	    setToolNotInstalled(true);
	    return true;
	}
	
	//unknown is always allowed. But wrong answers are not allowed
	if (isValid) {
	    return result.isValid() != SMTSolverResult.ThreeValuedTruth.FALSE; 
	} else {
	    return result.isValid() != SMTSolverResult.ThreeValuedTruth.TRUE;
	}
    }
    
    /**
     * check a problem file
     * @param filepath the path to the file
     * @return the resulttype of the external solver 
     */
    private SMTSolverResult checkFile(String filepath) throws IOException {
	ProofAggregate p = helper.parse(new File(filepath));
	Assert.assertTrue(p.getProofs().length == 1);
	Proof proof = p.getProofs()[0];	    
	Assert.assertTrue(proof.openGoals().size() == 1);		
	Goal g = proof.openGoals().iterator().next();
	SMTSolverResult toReturn = solver.run(g, 20, proof.getServices());
	return toReturn;
    }
    
}
