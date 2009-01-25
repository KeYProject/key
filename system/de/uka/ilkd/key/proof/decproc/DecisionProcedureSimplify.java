// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc;

import java.io.*;
import de.uka.ilkd.key.proof.Node;
import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.smt.ConstraintSet;


/**
 This class invokes the decision procedure
 "Simplify" which is part of ESC/Java by Compaq.
 */

public class DecisionProcedureSimplify extends AbstractDecisionProcedure {
    
    private static final String SIMPLIFY_COMMAND = "Simplify";

    public static final String SPACER = 
	"\\<---This is just a spacer between "+ 
	"sequent and Simplify input resp. Simplify output--->\\";
    
    static Logger logger = Logger.getLogger(DecisionProcedureSimplify.class.getName());

    public DecisionProcedureSimplify(Goal goal, Constraint userConstraint,
				     DecisionProcedureTranslationFactory dptf, 
				     Services services) {
        super(goal, userConstraint, dptf, services);
    }

    public DecisionProcedureSimplify(Node node, Constraint userConstraint,
				     DecisionProcedureTranslationFactory dptf, 
				     Services services) {
        super(node, userConstraint, dptf, services);
    }

    public static String execute(String input) throws IOException, 
	SimplifyException{
	File file = File.createTempFile("key-simplify", null);
	PrintWriter out = new PrintWriter(new FileWriter(file));
	out.println(input.replace('\n', ' '));
	out.close();
	
	Process p = Runtime.getRuntime().exec
	    (new String[]{ SIMPLIFY_COMMAND, file.getPath() });
	InputStream in = p.getInputStream();
	
	String response = read(in);
	in.close();
	
	file.delete();

	return response;
    }    

    /**
     * runs first the conversion into the Simplify syntax,
     * and runs Simplify via a temporary file.
     */
    protected DecisionProcedureResult runInternal(ConstraintSet constraintSet){
	return runInternal(constraintSet, false);
    }

    /**
     * runs first the conversion into the Simplify syntax,
     * and runs Simplify via a temporary file.
     * @param lightWeight true iff only quantifier free formulas shall be
     * considered.
     */
    protected DecisionProcedureResult runInternal(ConstraintSet constraintSet,
						  boolean lightWeight) {
	try {
	    SimplifyTranslation st = dptf.createSimplifyTranslation
		(node.sequent(), constraintSet, 
		 node.getRestrictedMetavariables(), this.services,
		 lightWeight);

	    /* It seems, there are problems with Process and
	     * Standard-IO. Even the simplest program doesn't work
	     * correctly with J2SE 1.4. But I haven't found a bug in
	     * Sun Bug Database. 
	     *
	     * try {
	     *     Process p = Runtime.getRuntime().exec("cat");
	     *     OutputStream out = p.getOutputStream();
	     *     InputStream in = p.getInputStream();
	     *     out.write("Hello World!\n".getBytes());
	     *     out.close();
	     *     BufferedReader rd = new BufferedReader(new InputStreamReader(in));
	     *     String s;
	     *     while ((s = rd.readLine()) != null) {
	     *         System.out.println("[" + s + "]");
	     *     }
	     * } catch (IOException ioe) {
	     *     ioe.printStackTrace();
	     * }
	     * 
	     * Instead of control with Standard-IO, I control the
	     * simplify process with a temporary file. -hs. */

	    String response = execute(st.getText());
/*
	    File file = File.createTempFile("key-simplify", null);
	    PrintWriter out = new PrintWriter(new FileWriter(file));
	    String input = st.getText().replace('\n', ' ');
	    out.println(input);
	    out.close();
	    
	    Process p = Runtime.getRuntime().exec
		(new String[]{ SIMPLIFY_COMMAND, file.getPath() });
	    InputStream in = p.getInputStream();

	    String response = read(in);
	    in.close();

	    file.delete();
*/
    
            // read the output from the command
	    logger.info("Here is what Simplify has to say:\n");
	    logger.info(response);

	    //This part is responsible for logging
	    String logdir = System.getProperty("key.simplify.logdir");
	    if (logdir == null || logdir.trim().length() == 0) {
		logger.warn("$KEY_SIMPLIFY_LOG_DIR is empty or non-existent. Logging (of proofs, not with log4j) of Simplify disabled.");
	    } else {
		try {
		    String logFileName = "simplify-log_" + getCurrentDateString() + ".log";
		    PrintWriter logfile = new PrintWriter
			(new BufferedWriter(new FileWriter(new File(logdir, logFileName))));
		    LogicPrinter sp = new LogicPrinter(new ProgramPrinter(logfile), 
						       NotationInfo.createInstance(),
						       services);
		    sp.printSequent(node.sequent());
		    logfile.print(sp.result().toString());
		    logfile.println(SPACER);
		    logfile.println(st.getText());
		    logfile.println(SPACER);
		    logfile.println(response);
		    logfile.close();
		} catch (IOException ioe) {
		    logger.error("error while trying to log:\n" + ioe);
		}
	    }
	    //End of logging part

	    if (response.indexOf("Valid.") > 0) {
		logger.info("Simplify has decided and found the formula to be valid.");
		return new DecisionProcedureResult
		    (true, response, constraintSet.chosenConstraint, st);
	    } else {
		return new DecisionProcedureResult
		    (false, response, constraintSet.chosenConstraint, st);
	    }
	} catch (IOException ioe) {
	    final String errorMessage = "\"Simplify\" execution failed:\n\n"+
		 ioe+"\n\n"+
		 "To make use of Simplify make sure that\n\n"+
		 "1. the binary is named Simplify (Linux) or "+
		 "Simplify.exe (Windows)\n"+
		 "2. the directory where the binary resides is in "+
		 "your $PATH variable\n"+
		 "3. the binary has executable file permissions (Linux only).";
            throw new RuntimeException(errorMessage);
	} catch (SimplifyException se) {
	    return new DecisionProcedureResult(false, se.toString(), 
					       constraintSet.chosenConstraint);
        }	
    }

}
