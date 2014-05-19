// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.smt.test;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;

import junit.framework.Assert;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.smt.ProofDependentSMTSettings;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverType;

class SMTSettings implements de.uka.ilkd.key.smt.SMTSettings{


	public long getGlobalBound(){
		return 0;
	}

    @Override
    public int getMaxConcurrentProcesses() {
	return 1;
    }

    @Override
    public int getMaxNumberOfGenerics() {
	return 2;
    }

    @Override
    public String getSMTTemporaryFolder() {
	return   PathConfig.getKeyConfigDir()
	    + File.separator + "smt_formula";
    }

    @Override
    public Collection<Taclet> getTaclets() {
	return null;
    }

    @Override
    public long getTimeout() {
	return 300000;
    }

    @Override
    public boolean instantiateNullAssumption() {
	return true;
    }

    @Override
    public boolean makesUseOfTaclets() {
	return false;
    }

    @Override
    public boolean useExplicitTypeHierarchy() {
	return false;
    }
    
    @Override
    public boolean useBuiltInUniqueness() {
         return false;
    }

    @Override
    public boolean useAssumptionsForBigSmallIntegers() {
	return false;
    }

    @Override
    public boolean useUninterpretedMultiplicationIfNecessary() {
	return false;
    }

@Override
public long getMaximumInteger() {

        return ProofDependentSMTSettings.getDefaultSettingsData().maxInteger;
}

@Override
public long getMinimumInteger() {

        return ProofDependentSMTSettings.getDefaultSettingsData().minInteger;
}

@Override
public String getLogic() {
	return "AUFLIA";
}

@Override
public boolean checkForSupport() {
	return false;
}

@Override
public long getIntBound() {
	return 3;
}

@Override
public long getHeapBound() {
	return 3;
}

@Override
public long getSeqBound() {
	return 3;
}

@Override
public long getObjectBound() {
	return 3;
}

@Override
public long getLocSetBound() {
	return 3;
}

@Override
public boolean invarianForall() {
	// TODO Auto-generated method stub
	return false;
}

    
}

public abstract class TestSMTSolver extends TestCommons {
    

    private static HashMap<String,ProofAggregate> proofs = new HashMap<String,ProofAggregate>();
   
    public static final String testFile = System.getProperty("key.home")
    + File.separator + "examples"
    + File.separator + "_testcase"
    + File.separator + "smt"
    + File.separator;

    protected void setUp() {

    }
    

    @Override
    protected void tearDown() throws Exception {

    }
    

    
    
    /**
     * returns the solver that should be tested.
     * @return the solver to be tested.
     */
    public abstract SolverType getSolverType();


    public abstract boolean toolNotInstalled();




    
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
            if(getSolverType().supportsIfThenElse())
                    Assert.assertTrue(correctResult(testFile + "termite1.key", true));
    }
    
    public void testTermlIte2() {
            if(getSolverType().supportsIfThenElse())
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
    
    public void testBSum1() {
        Assert.assertTrue(correctResult(testFile + "bsum1.key", true));
    }
    
    public void testBSum2() {
        Assert.assertTrue(correctResult(testFile + "bsum2.key", true));
    }
    
    public void testBSum3() {
        Assert.assertTrue(correctResult(testFile + "bsum3.key", false));
    }
    
    public void testBProd1() {
        Assert.assertTrue(correctResult(testFile + "bprod1.key", true));
    }
    
    public void testBProd2() {
        Assert.assertTrue(correctResult(testFile + "bprod2.key", true));
    }
    
    public void testBProd3() {
        Assert.assertTrue(correctResult(testFile + "bprod3.key", false));
    }
    
//    public void testBinderPred1() {
//        Assert.assertTrue(correctResult(testFile + "binder2.key", true));
//    }
    
    public void testBinderPred2() {
        Assert.assertTrue(correctResult(testFile + "binder4.key", true));
    }
    
    public void testBinderPred3() {
        Assert.assertTrue(correctResult(testFile + "binder5.key", true));
    }
    
    /*public void testAdd2() {
	Assert.assertTrue(correctResult(testFile + "add2.key", false));
    }*/
    
    //not linear, so yices throws exception
   /* public void testMult1() {
	Assert.assertTrue(correctResult(testFile + "mult1.key", true));
    }*/
    
    protected boolean correctResult(String filepath, boolean isValid) {
	if (toolNotInstalled()) {
	    return true;
	}

	SMTSolverResult result;
	try {
	    result = checkFile(filepath);
	} catch (IOException e) {

	    //must not happen!!
	    System.out.println("Warning: " + this.getSolverType().getName() 
                               + " produced error!!.");
	
	    e.printStackTrace();
	    //setToolNotInstalled(true);
	    return true;
	}
	
	//System.gc();
	
	//unknown is always allowed. But wrong answers are not allowed
	if (isValid && result != null) {
	    return result.isValid() != SMTSolverResult.ThreeValuedTruth.FALSIFIABLE; 
	} else {
	    return result.isValid() != SMTSolverResult.ThreeValuedTruth.VALID;
	}
    }
    

    
    /**
     * check a problem file
     * @param filepath the path to the file
     * @return the resulttype of the external solver 
     */
    private SMTSolverResult checkFile(String filepath) throws IOException {
	ProofAggregate p;
        
  
  
       
        if(!proofs.containsKey(filepath)){
            File file =  new File(filepath);
            p = parse(file);
            proofs.put(filepath, p);
        }else{
            p = proofs.get(filepath);
        }
	
	Assert.assertTrue(p.getProofs().length == 1);
	Proof proof = p.getProofs()[0];	    
	Assert.assertTrue(proof.openGoals().size() == 1);		
	Goal g = proof.openGoals().iterator().next();

	SolverLauncher launcher = new SolverLauncher(new SMTSettings());
	
	SMTProblem problem = new SMTProblem(g);

	
	    launcher.launch(problem, proof.getServices(),getSolverType());
	

	
	
	return problem.getFinalResult();
    }
    
}