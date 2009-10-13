// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.smt.test;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

import junit.framework.Assert;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.smt.CVC3Solver;
import de.uka.ilkd.key.smt.DefaultTacletSetTranslation;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SimplifySolver;

import de.uka.ilkd.key.smt.TacletSetTranslation;
import de.uka.ilkd.key.smt.YicesSolver;
import de.uka.ilkd.key.smt.Z3Solver;


/**
 * @author niederma
 *
 */
public class TestSMTWithTaclets extends TestTaclet  {
    
    private static String VALID = "valid";
    private static String INVALID = "not valid";
    private static String UNKNOWN = "unknown";
    private static String NOTAVAILABLE = "not installed";
    

      

    
 
    /**Set this variable to <code>true</code>, if you want a output file. Change this variable directly in code.*/
    private boolean storeToFile = true;
   
    protected void setUp() {

    }
    
    
    /**
     * Tests some files (see <code>collectFilenames</code>) with problems that can be sovled by external provers only by means of taclets.
     * @throws IOException
     */
    public void testTaclets() throws IOException {
	ArrayList<SMTSolver> solvers = getRules();

	// First check whether the solvers are installed.
	for(SMTSolver solver : solvers){
	    solver.isInstalled(true);
	}
	
	String [] files = collectFilenames();
	boolean use[] = {false,true};
	
	ArrayList<ArrayList<String>> result = new ArrayList<ArrayList<String>>(); 
	
	

	for(String file : files){
	    for(int i=0; i < 2; i++){
		ArrayList<String> solverRes = new ArrayList<String>(); 
		result.add(solverRes);
		solverRes.add(Boolean.toString(use[i]));


		for(SMTSolver solver  : solvers){
		    if(!solver.isInstalled(false)){
			solverRes.add(NOTAVAILABLE);
			continue;
		    }
		    solver.useTaclets(use[i]);

		    String res="";

		    res = checkFile(solver,folder+file);


		    solverRes.add(res);


		    if(use[i]){
			Assert.assertTrue("The problem "+file+ " can not be solved.",(res.equals(VALID)));
		    }else{
			Assert.assertTrue("The problem "+file+" can be solved without using taclets.",res.equals(UNKNOWN) || res.equals(INVALID)); 
		    }		 
		}	      
	    }

	    if(this.storeToFile){
		storeToFile(result,file,solvers,folder+"smtTacletTestResults.csv");
	    }
	}
    }
    
    

    
    private String translateResult(SMTSolverResult r) {
	if (r.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE) {
	    return VALID;
	} else if (r.isValid() == SMTSolverResult.ThreeValuedTruth.UNKNOWN) {
	    return UNKNOWN;
	} else if (r.isValid() == SMTSolverResult.ThreeValuedTruth.FALSE) {
	    return INVALID;
	} else {
	    Assert.assertTrue(false);
	    return UNKNOWN;
	}
    }
    

    private void storeToFile(ArrayList<ArrayList<String>> result, String file,ArrayList<SMTSolver> solvers,
            String dest) {
	
	String toStore = "Filename\t\t\tused taclets\t\t\t";
	for(SMTSolver solver : solvers){
	    toStore = toStore+solver.name()+"\t\t\t";
	}
	toStore = toStore+"\n";
	
	for(ArrayList<String> solverRes : result){
	    String temp = file+"\t\t\t";
	    for(String res : solverRes){
		temp = temp + res+ "\t\t\t";}
	    temp=temp+"\n";

	    toStore = toStore+temp;
	    
	}
	FileWriter fw;
	try {
	    fw = new FileWriter(dest);
	    fw.write(toStore);
	    fw.close();
	} catch (IOException e) {
	    System.out.println("Error while writing result file");
	}

	
    }

    /**
     * Loads the proof and taclets. Starts the external prover.
     */
    private String checkFile(SMTSolver solver, String filepath) throws IOException{
	ProofAggregate p = parse(new File(filepath));
	
	TacletSetTranslation translation = new DefaultTacletSetTranslation();
	translation.addHeuristic("smt_axiom_not_verified");
	translation.setTacletSet(getTaclets());	
	solver.setTacletSetTranslation(translation);
	

	Assert.assertTrue(p.getProofs().length == 1);
	Proof proof = p.getProofs()[0];	    
	Assert.assertTrue(proof.openGoals().size() == 1);
	
	Goal g = proof.openGoals().iterator().next();
	SMTSolverResult result = solver.run(g, 50, proof.getServices());
	return translateResult(result);
	
    }
    
    
    private ArrayList<SMTSolver> getRules() {
	ArrayList<SMTSolver> toReturn = new ArrayList<SMTSolver>();
	toReturn.add(new SimplifySolver());
	toReturn.add(new Z3Solver());
	toReturn.add(new YicesSolver());
	toReturn.add(new CVC3Solver());
	return toReturn;
    }
    

    
    
    
    
    private String[] collectFilenames(){
	String [] res = {"booleanProblems.key"};
	return res;
    }
    
 
    
   
  
}
