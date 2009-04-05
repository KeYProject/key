//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.io.*;
import java.util.Calendar;
import java.util.Date;
import java.util.Timer;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.apache.log4j.Logger;


public abstract class AbstractSMTSolver implements SMTSolver {


    private static final Logger logger = Logger
	    .getLogger(AbstractSMTSolver.class.getName());

    /**
     * The path for the file
     */
    private static final String fileDir = PathConfig.KEY_CONFIG_DIR
	    + File.separator + "smt_formula";
    
    
    /**
     * Get the command for executing the external prover.
     * @param filename the location, where the file is stored.
     * @param formula the formula, that was created by the translator
     * @return Array of Strings, that can be used for executing an external decider.
     */
    protected abstract String[] getExecutionCommand(String filename,
	    				            String formula);
    
    
    /**
     * @param text the String answered by the external programm.
     * @return A SMTSolverResult containing all information of the interpretation.
     */
    protected abstract SMTSolverResult interpretAnswer(String text);

    private static String toStringLeadingZeros(int n, int width) {
	String rv = "" + n;
	while (rv.length() < width) {
	    rv = "0" + rv;
	}
	return rv;
    }

    /**
     * Constructs a date for use in log filenames.
     */
    private static String getCurrentDateString() {
	Calendar c = Calendar.getInstance();
	StringBuffer sb = new StringBuffer();
	String dateSeparator = "-";
	String dateTimeSeparator = "_";
	sb.append(toStringLeadingZeros(c.get(Calendar.YEAR), 4)).append(
		dateSeparator).append(
		toStringLeadingZeros(c.get(Calendar.MONTH) + 1, 2)).append(
		dateSeparator).append(
		toStringLeadingZeros(c.get(Calendar.DATE), 2)).append(
		dateTimeSeparator).append(
		toStringLeadingZeros(c.get(Calendar.HOUR_OF_DAY), 2) + "h")
		.append(toStringLeadingZeros(c.get(Calendar.MINUTE), 2) + "m")
		.append(toStringLeadingZeros(c.get(Calendar.SECOND), 2) + "s")
		.append('.').append(
			toStringLeadingZeros(c.get(Calendar.MILLISECOND), 2));
	return sb.toString();
    }

    /**
     * store the text to a file.
     * @param text the text to be stored.
     * @return the path, where the file was stored to.
     */
    private final String storeToFile(String text) throws IOException {
	String loc = fileDir + getCurrentDateString();
	new File(fileDir).mkdirs();
	BufferedWriter out = new BufferedWriter(new FileWriter(loc));
	out.write(text);
	out.close();

	return loc;
    }


    /** Read the input until end of file and return contents in a
     * single string containing all line breaks. */
    private static String read(InputStream in) throws IOException {
	BufferedReader reader = new BufferedReader(new InputStreamReader(in));
	StringBuffer sb = new StringBuffer();
	int x = reader.read();
	while (x > -1) {
	    sb.append((char) x);
	    x = reader.read();
	}
	return sb.toString();
    }

    /**
     * Run this solver on a goal.
     * @param goal The goal that should be proven.
     * @param timeout The maximum time, that should be used for proving.
     * 		If it takes longer, UNKNOWN is returned.
     * @param services the service object belonging to this goal.
     */
    public final SMTSolverResult run(Goal goal, int timeout, Services services) {
	SMTSolverResult toReturn;
		
	SMTTranslator trans = this.getTranslator(services);
	
	try {
	    String s = trans.translate(goal.sequent(), services).toString();
	    toReturn = this.run(s, timeout, services);
    	} catch (IllegalFormulaException e) {
	    toReturn = SMTSolverResult.NO_IDEA;
	    logger.debug("The formula could not be translated.", e);
	    //throw new RuntimeException("The formula could not be translated.\n" + e.getMessage());
	}
    	
    	return toReturn;
    }


    /**
     * Run the solver on a term.
     * @param t the term to be proven.
     * @param timeout the maximum time to be used for proving.
     * 		If the time elapses, UNKNOWN is returned.
     */
    public final SMTSolverResult run(Term t, int timeout, Services services) {
	assert t.sort() == Sort.FORMULA;
	SMTSolverResult toReturn;
		
	SMTTranslator trans = this.getTranslator(services);
	
	try {
	    String s = trans.translate(t, services).toString();
	    toReturn = this.run(s, timeout, services);
    	} catch (IllegalFormulaException e) {
	    toReturn = SMTSolverResult.NO_IDEA;
	    logger.debug("The formula could not be translated.", e);
	    //throw new RuntimeException("The formula could not be translated.\n" + e.getMessage());
	}
    	
    	return toReturn;
    }

    /**
     * run the solver on a formula.
     * @param formula The formula to be proven in syntax, this solver supports.
     * 		Ususally it is not recommended to call this directly!
     * @param timeout
     * 		The maximum time, that should be used for the proof.
     * @param services The services object to use.
     */
    public final SMTSolverResult run(String formula, 
	    	                     int timeout, 
	    			     Services services) {
	SMTSolverResult toReturn;
	
	try {
	    //store the translation to a file                                
	    final String loc = this.storeToFile(formula);
	    
	    //get the commands for execution
	    String[] execCommand = this.getExecutionCommand(loc, formula);

	    try {
		Process p = Runtime.getRuntime().exec(execCommand);
		ExecutionWatchDog tt = new ExecutionWatchDog(timeout, p);
		Timer t = new Timer();
		t.schedule(tt, new Date(System.currentTimeMillis()), 1000);
		try {
		    p.waitFor();
		    if (tt.wasInterrupted()) {
			logger.debug(
				"Process for smt formula proving interrupted because of timeout.");
		    }
		} catch (InterruptedException f) {
		    logger.debug(
			    "Process for smt formula proving interrupted.",
			    f);
		    //System.out.println("process was interrupted");
		} finally {
		    t.cancel();
		}

		if (p.exitValue() != 0) {
		    //the process was terminated by force.
		    toReturn = SMTSolverResult.NO_IDEA;
		} else {
		    //the process terminated as it sould
		    InputStream in = p.getInputStream();
		    String text = read(in);
   
		    logger.debug("Answer for created formula: ");
		    logger.debug(text);
		    in.close();
		    
		    toReturn = this.interpretAnswer(text);
		}
	    } catch (IOException e) {
		logger.error(
			"The program for proving a Formula with external tool could not be executed.",
			e);
		throw new RuntimeException(e.getMessage() + "\nMake sure the command is in your PATH variable.");
	    } finally {
		//remove the created file
		File f = new File(loc);
		f.delete();
	    }
	} catch (IOException e) {
	    logger.error("The file with the formula could not be written.",
			e);
	    throw new RuntimeException(e.getMessage());
	}
	
	return toReturn;
    }
    
}
