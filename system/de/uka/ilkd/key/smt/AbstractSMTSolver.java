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

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;


public abstract class AbstractSMTSolver implements SMTSolver {


    private static final Logger logger = Logger
	    .getLogger(AbstractSMTSolver.class.getName());

    /**
     * The path for the file
     */
    private static final String fileDir = PathConfig.KEY_CONFIG_DIR
	    + File.separator + "smt_formula";

    /**
     * the file base name to be used to store the SMT translation
     */
    private static final String FILE_BASE_NAME = "smt_formula";
    
    
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
     * @return the path where the file was stored to.
     */
    private final File storeToFile(String text) throws IOException {
	// create directory where to put the files marked as delete on exit
	final File smtFileDir = new File(fileDir);
	smtFileDir.mkdirs();
	smtFileDir.deleteOnExit();
	
	// create the actual file marked as delete on exit
	final File smtFile = new File(smtFileDir, FILE_BASE_NAME + getCurrentDateString());
	smtFile.deleteOnExit();
	
	// write the content out to the created file
	final BufferedWriter out = new BufferedWriter(new FileWriter(smtFile));
	out.write(text);
	out.close();

	return smtFile;
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
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public final SMTSolverResult run(Goal goal, int timeout, Services services) throws IOException {
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
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public final SMTSolverResult run(Term t, int timeout, Services services) throws IOException {
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
     * @throws IOException if the external prover could not be found, executed or if the SMT translation
     * could not be written to a file
     */
    public final SMTSolverResult run(String formula, 
	    	                     int timeout, 
	    			     Services services) throws IOException{
	SMTSolverResult toReturn;
	
	final File loc;
	try {
	    //store the translation to a file                                
	    loc = this.storeToFile(formula);
	} catch (IOException e) {
	    logger.error("The file with the formula could not be written.", e);
	    final IOException io = new IOException("Could not create or write the input file " +
		    "for the external prover. Received error message:\n" + e.getMessage());
	    io.initCause(e);
	    throw io;
	} 

	//get the commands for execution
	String[] execCommand = this.getExecutionCommand(loc.getAbsolutePath(), formula);

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
		//the process terminated as it should
		InputStream in = p.getInputStream();
		String text = read(in);

		logger.debug("Answer for created formula: ");
		logger.debug(text);
		in.close();

		toReturn = this.interpretAnswer(text);
	    }
	} catch (IOException e) {
	    String cmdStr = "";
	    for (String cmd : execCommand) {
		cmdStr += cmd + " ";
	    }
	    IOException ioe = new IOException("Invocation of decision procedure\n\t\t" +
		    this.name() + "\n with command \n\t\t" + cmdStr + "\n" +  
		    "failed. The most common (but not all) reasons for this error are:\n" +
		    "\n 1. the directory where you put the executable of the decision procedure is not in your PATH.\n " +
		    "\t    Solution: Add the directory to your PATH environment variable." +
		    "\n 2. we expect a different name than your executable " +
		    "(prior to KeY 1.5 and later we expected 'Simplify' instead of 'simplify')" +
		    "\n\t Solution: Change the name to " + (execCommand != null && execCommand.length > 0 ? 
		        	execCommand[0] : "expected name") +
		    "\n 3. you have not the permission to execute the decision procedure." +
		    "\n\t Solution: *nix-like systems: try 'chmod u+x <path_to_executable>/<executable_filename>" +
		    "\n 4. you use a too new or too old version of the decision procedure and the command " +
		        "line parameters changed." +
		    "\n\t Solution: Install a supported version (see http://www.key-project.org)\n" +
		    "\n Original Error-Message: " + e.getMessage());
	    ioe.initCause(e);
	    throw ioe;
	} 

	return toReturn;
    }
    
}
