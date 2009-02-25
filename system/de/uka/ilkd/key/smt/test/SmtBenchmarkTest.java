package de.uka.ilkd.key.smt.test;

import junit.framework.Assert;
import junit.framework.TestCase;
import java.io.File;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.util.ArrayList;


import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.smt.SimplifySolver;
import de.uka.ilkd.key.smt.SmtSolver;
import de.uka.ilkd.key.smt.YicesSmtSolver;
import de.uka.ilkd.key.smt.Z3Solver;
import de.uka.ilkd.key.util.HelperClassForTests;

public class SmtBenchmarkTest extends TestCase implements FilenameFilter{

    private static String VALID = "valid";
    private static String INVALID = "not valid";
    private static String UNKNOWN = "unknown";
    private static String NOTAVAILABLE = "not installed";
    private int maxExecutionTime = 10;
    
    public static final String folderPath = System.getProperty("key.home")
    + File.separator + "examples"
    + File.separator + "toolBenchmark"
    + File.separator + "keyFiles"
    + File.separator;
    
    public void testBenchmarks() {
	String[] files = this.collectFilenames();
	ArrayList<SmtSolver> rules = getRules();
	
	ArrayList<ArrayList<Proof>> toProof = this.loadGoals(rules.size(), files);
	ArrayList<ArrayList<String>> results = new ArrayList<ArrayList<String>>();
	System.out.println();
	for (int i = 0; i < toProof.size(); i++) {
	    results.add(proofOneGoal(toProof.get(i), rules));
	}
	this.printResults(files, rules, results);
    }
    
    private void printResults(String[] sources, ArrayList<SmtSolver> solver, ArrayList<ArrayList<String>> results) {
	String output = "";
	//print header
	output = "Problem\tFile\t";
	for (int i = 0; i < solver.size(); i++) {
	    output = output + solver.get(i).displayName() + "\t\t";
	}
	output = output + "\n";
	
	//print one line for each problem
	for (int i = 0; i < sources.length; i++) {
	    
	    ArrayList<String> problemResults = results.get(i);
	    if (this.hasProblem(problemResults)) {
		output = output + "x\t";
	    } else {
		output = output + "\t";
	    }
	    output = output + sources[i] + "\t";
	    //print the results for the solver
	    
	    for (int j = 0; j < problemResults.size(); j++) {
		output = output + problemResults.get(j) + "\t";
	    }
	    output = output + "\n";
	}
	storeResults(output);
    }
    
    private void storeResults(String result) {
	FileWriter fw;
	try {
	    fw = new FileWriter(folderPath + "smtBenchmarkResults.csv");
	    fw.write(result);
	    fw.close();
	} catch (IOException e) {
	    System.out.println("Error while writing result file");
	}
	
    }
    
    private boolean hasProblem(ArrayList<String> results) {
	boolean hasValid = false;
	boolean hasInvalid = false;
	for (int i = 0; i < results.size(); i++) {
	    if (results.get(i).equals(VALID)) {
		hasValid = true;
	    } else if (results.get(i).equals(INVALID)) {
		hasInvalid = true;
	    }
	}
	return hasValid && hasInvalid;
    }
    
    private ArrayList<String> proofOneGoal(ArrayList<Proof> goals, ArrayList<SmtSolver> rules) {
	ArrayList<String> toReturn = new ArrayList<String>();
	for (int i = 0; i < goals.size(); i++) {
	    System.out.print(".");
	    SmtSolver s = rules.get(i);
	    Proof p = goals.get(i);
	    try {
		long time = System.currentTimeMillis();
	    	SmtSolver.RESULTTYPE result = s.isValid(p.openGoals().iterator().next(), maxExecutionTime, p.getServices());
	    	time = System.currentTimeMillis() - time;
	    	time = time / 100;
	    	toReturn.add("" + time/10 + "." + time%10);
		toReturn.add(this.translateResult(result));
	    } catch (RuntimeException e) {
		toReturn.add(NOTAVAILABLE);
		toReturn.add(NOTAVAILABLE);
	    }
	    
	    
	}
	return toReturn;
    }
    
    
    private String translateResult(SmtSolver.RESULTTYPE r) {
	if (r == SmtSolver.RESULTTYPE.VALID) {
	    return VALID;
	} else if (r == SmtSolver.RESULTTYPE.UNKNOWN) {
	    return UNKNOWN;
	} else if (r == SmtSolver.RESULTTYPE.INVALID) {
	    return INVALID;
	} else {
	    Assert.assertTrue(false);
	    return UNKNOWN;
	}
    }
    
    private ArrayList<ArrayList<Proof>> loadGoals(int multiplicity, String[] sources) {
	ArrayList<ArrayList<Proof>> toReturn = new ArrayList<ArrayList<Proof>>();
	for (int i = 0; i < sources.length; i++) {
	    String path = folderPath + sources[i];
	    toReturn.add(getSingleGoal(path, multiplicity));
	}
	return toReturn;
    }
    
    /**
     * load the goal specified by sopurce multiplicity times.
     * @param source the path to the file that stores the goal.
     * @param multiplicity amount of times, the goal is needed.
     * @return arraylist of the loaded goals.
     */
    private ArrayList<Proof> getSingleGoal(String source, int multiplicity) {
	ArrayList<Proof> toReturn = new ArrayList<Proof>();
	for (int i = 0; i < multiplicity; i++) {
	    HelperClassForTests x = new HelperClassForTests();	
	    ProofAggregate p = x.parse(new File(source));
	    Assert.assertTrue(p.getProofs().length == 1);
	    Proof proof = p.getProofs()[0];	    
	    toReturn.add(proof);
	}
	return toReturn;
    }
    
    
    /**
     * create all Solver, that should be tested
     * @return the Rules, that should be tested.
     */
    private ArrayList<SmtSolver> getRules() {
	ArrayList<SmtSolver> toReturn = new ArrayList<SmtSolver>();
	toReturn.add(new SimplifySolver());
	toReturn.add(new Z3Solver());
	toReturn.add(new YicesSmtSolver());
	return toReturn;
    }
    
    private String[] collectFilenames() {
	File f = new File(folderPath);
	Assert.assertTrue(f.isDirectory());
	
	String[] fl = f.list(this);
	
	return fl;
    }
    
    public boolean accept(File f, String name) {
	if (name.substring(name.length()-4, name.length()).equals(".key")) {
	    return true;
	} else {
	    return false;
	}
    }
}
