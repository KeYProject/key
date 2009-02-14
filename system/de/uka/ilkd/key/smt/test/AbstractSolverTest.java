package de.uka.ilkd.key.smt.test;

import java.io.File;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.smt.SmtSolver;
import de.uka.ilkd.key.util.HelperClassForTests;
import junit.framework.Assert;
import junit.framework.TestCase;

public abstract class AbstractSolverTest extends TestCase {

    SmtSolver solver;
    
    public static final String testFile = System.getProperty("key.home")
    + File.separator + "examples"
    + File.separator + "_testcase"
    + File.separator + "smt"
    + File.separator;

    
    protected void setUp() {
	solver = this.getSolver();
    }
    
    /**
     * returns the solver that should be tested.
     * @return the solver to be tested.
     */
    public abstract SmtSolver getSolver();
    
    
    public void testCount() {
	Assert.assertTrue(checkFile(testFile + "count.key") == SmtSolver.RESULTTYPE.VALID);
    }
    
    public void testSameName() {
	SmtSolver.RESULTTYPE result = checkFile(testFile + "sameName1.key");
	Assert.assertTrue(result == SmtSolver.RESULTTYPE.UNKNOWN || result == SmtSolver.RESULTTYPE.INVALID);
    }
    
    public void testMv3() {
	SmtSolver.RESULTTYPE result = checkFile(testFile + "mv3.key");
	Assert.assertTrue( result == SmtSolver.RESULTTYPE.UNKNOWN || result == SmtSolver.RESULTTYPE.INVALID);
    }
    
    public void testExist() {
	SmtSolver.RESULTTYPE result = checkFile(testFile + "exist1.key");
	Assert.assertTrue( result == SmtSolver.RESULTTYPE.VALID );
    }
    
    public void testSubsorts() {
	SmtSolver.RESULTTYPE result = checkFile(testFile + "subsorts.key");
	Assert.assertTrue( result == SmtSolver.RESULTTYPE.VALID );
    }
    
    /**
     * check a problem file
     * @param filepath the path to the file
     * @return the resulttype of the external solver 
     */
    private SmtSolver.RESULTTYPE checkFile(String filepath) {	
	HelperClassForTests x = new HelperClassForTests();	
	ProofAggregate p = x.parse(new File(filepath));
	SmtSolver.RESULTTYPE toReturn = SmtSolver.RESULTTYPE.UNKNOWN;
	Assert.assertTrue(p.getProofs().length == 1);
	Proof proof = p.getProofs()[0];	    
	Assert.assertTrue(proof.openGoals().size() == 1);		
	Goal g = proof.openGoals().iterator().next();
	toReturn = solver.isValid(g, 60, proof.getServices());
	
	return toReturn;
    }
    
}
