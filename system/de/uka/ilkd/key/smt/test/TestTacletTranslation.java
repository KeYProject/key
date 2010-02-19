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
import java.util.Collection;
import java.util.HashSet;

import javax.jws.soap.SOAPBinding.Use;

import junit.framework.Assert;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.DecisionProcedureSettings;
import de.uka.ilkd.key.gui.TacletTranslationSettings;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.AbstractSMTSolver;
import de.uka.ilkd.key.smt.CVC3Solver;
import de.uka.ilkd.key.smt.IllegalFormulaException;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SimplifySolver;
import de.uka.ilkd.key.smt.YicesSolver;
import de.uka.ilkd.key.smt.Z3Solver;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem;
import de.uka.ilkd.key.smt.taclettranslation.UsedTaclets;
import de.uka.ilkd.key.smt.taclettranslation.TreeItem.SelectionMode;





public class TestTacletTranslation extends TestTaclet {
    

    
    private final SMTSolver simplify = new SimplifySolver();
    private final SMTSolver cvc3 = new CVC3Solver();
    private final SMTSolver z3 = new Z3Solver();
    private final SMTSolver yices = new YicesSolver();
    
    
   
    enum SolveType {
		/**The problem can be solved without taclets. */
		WITHOUT_TACLETS, 
		/**The problem can be solved ONLY by means of taclets.*/
		WITH_TACLETS_ONLY, 
		/**The problem can not be solved by externals provers.
		 * (This does not mean that the problem is not solvable)*/ 
		NOT_SOLVABLE};


    
    /**
     * In UsedTaclets.java all taclets are encoded that are supported.
     * This test ensures that every taclet's name mentioned in <code>UsedTaclet</code>
     * has a corresponding taclet.  
     */
    public void testNameCorrespondsToTaclet(){
	Collection<String> subset = UsedTaclets.INSTANCE.getTacletNames();
	HashSet<String> set = this.getTacletNames();
	for(String s : subset){
	    assertTrue("There is no taclet that corresponds to the name " + s +".", set.contains(s));
	}
    }
    
    
    public void testBoolean(){
	test("booleanProblems.key",SolveType.WITH_TACLETS_ONLY,UsedTaclets.Category.BOOLEAN_RULES);
    }
    
    public void testInteger(){
	test("integerProblems.key",SolveType.WITH_TACLETS_ONLY,UsedTaclets.Category.PROOF_INDEPENDENT,yices,z3);
    }
    
    public void testCasts(){
	test("castProblems.key",SolveType.WITH_TACLETS_ONLY,UsedTaclets.Category.CAST_OPERATOR);
    }
    
    public void testArrayLength(){
	test("arrayLength.key",SolveType.WITH_TACLETS_ONLY,UsedTaclets.Category.ARRAY_LENGTH);
    }
   
    
    public void testComplexProblem1(){
	test("complexProblem.key",SolveType.WITH_TACLETS_ONLY,UsedTaclets.Category.ALL_SUPPORTED,yices);
    }
    
    public void testComplexProblem2(){
	test("complexProblem2.key",SolveType.WITH_TACLETS_ONLY,UsedTaclets.Category.ALL_SUPPORTED,yices);
    }
    
    public void testAttributes(){
	test("attributes.key",SolveType.WITH_TACLETS_ONLY,UsedTaclets.Category.ONLY_CREATED_OBJECTS_ARE_REFERENCED_NORMAL);
    }
    
    
    
    
   
    
 
    @Override
    protected void setUp() throws Exception {
	TacletTranslationSettings.getInstance().setMaxGeneric(4);
    }
	
     
    private void test(String filename, SolveType type, UsedTaclets.Category cat){
	test(filename, type, cat,(SMTSolver [])null);
    }

    private void test(String filename, SolveType type, UsedTaclets.Category cat, SMTSolver ... only){
	
	ArrayList<SMTSolver> solvers = getRules(only);
	for (SMTSolver solver : solvers) {
	    solver.isInstalled(true);
	}

	UsedTaclets.INSTANCE.selectCategory(cat);
	
	boolean use [] = {true, false};
	
	for(int i=0; i < 2; i++){
	     ArrayList<String> solverRes = new ArrayList<String>();
	     solverRes.add(Boolean.toString(use[i]));
	     
	     for (SMTSolver solver : solvers) {
		    if (!solver.isInstalled(false)) {
			continue;
		    }
		    solver.useTaclets(use[i]);

	
		    checkFile(solver, folder + filename, type, use[i]);
	


		}
	}

    }
    
    
    


   

    /**
     * Loads the proof and taclets. Starts the external prover.
     */
    private void checkFile(SMTSolver solver, String filepath, SolveType type , boolean use)
	   
	    {
	ProofAggregate p = parse(new File(filepath));

	boolean solvable = (type == SolveType.WITH_TACLETS_ONLY && use) ||
	    (type == SolveType.WITHOUT_TACLETS && !use);
	
	String error = "\n\n"+
	       "problem:" + filepath +"\n"+	
	       "solver: " + solver.name()+"\n"+
	      
	       "taclets were used: " + use + "\n"+
	       "solve type: " + type.toString() +"\n"+
	       "-> solvable: " + solvable+"\n";


	((AbstractSMTSolver) solver).setTacletsForTest(getTaclets());

	Assert.assertTrue(p.getProofs().length == 1);
	Proof proof = p.getProofs()[0];
	Assert.assertTrue(proof.openGoals().size() == 1);

	Goal g = proof.openGoals().iterator().next();
	SMTSolverResult result = null;
	
	try{
	     result = solver.run(g, 5000, proof.getServices());
	}catch(Exception e){
	    assertTrue("Error while executing the solver: "+ error + e.getMessage(),false);
	    return;
	}
	

	
	error += "result: " + result.isValid().toString()+"\n";
		       
	
	
	    
	   	
	assertFalse("type 1: " + error,result.isValid() == SMTSolverResult.ThreeValuedTruth.UNKNOWN && solvable);
	assertFalse("type 2: " + error,result.isValid() == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE && solvable);
	assertFalse("type 3: " + error,result.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE && !solvable);
	

	
    }

    private ArrayList<SMTSolver> getRules(SMTSolver [] only) {
	ArrayList<SMTSolver> toReturn = new ArrayList<SMTSolver>();
	
	add(toReturn,only,z3);
	add(toReturn,only,simplify);
	add(toReturn,only,yices);
	add(toReturn,only,cvc3);
	
	return toReturn;
    }
    
    private boolean add(ArrayList<SMTSolver> toReturn, SMTSolver [] only, SMTSolver o){
	if(only != null){
	for(SMTSolver solver : only){
	    if(solver == o){
		toReturn.add(o);   
		return true;
	    }
	}}else{
	    toReturn.add(o);  
	    return true;
	}
	
	return false;
    }


    
    
    
    
    /**
     * The other direction of <code>testNameCorrespondesToTaclet</code>
     */
    public void testTacletsCorrespondesToNames(){
	
    }
    

   
}
