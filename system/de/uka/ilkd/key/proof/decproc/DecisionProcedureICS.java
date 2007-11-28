// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.decproc;

import java.io.*;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Goal;


/**
   This class invokes the decision procedure "ICS".
*/

public class DecisionProcedureICS extends AbstractDecisionProcedure {
    
    private static final String ICS_COMMAND = "ics";

    public static final String SPACER = 
	"\\<---This is just a spacer between "+ 
	"sequent and ICS input resp. ICS output--->\\";
    
    static Logger logger = Logger.getLogger(DecisionProcedureICS.class.getName());

    public DecisionProcedureICS(Goal goal, Constraint userConstraint,
				DecisionProcedureTranslationFactory dptf, Services services) {
		super(goal, userConstraint, dptf, services);
	}
    

    /**
     * runs first the conversion into the Simplify syntax,
     * and runs Simplify via a temporary file.
     */
    protected DecisionProcedureResult runInternal(ConstraintSet constraintSet,
						  boolean lightWeight) {
	try {
	    ICSTranslation st = dptf.createICSTranslation
		(goal.sequent(), constraintSet, 
		 goal.node().getRestrictedMetavariables(), this.services);

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

	    File file = File.createTempFile("key-ics", null);
	    PrintWriter out = new PrintWriter(new FileWriter(file));
	    out.println(st.getText());
	    
	    logger.info(st.getText());
	    
	    out.close();
	    
	    Process p = Runtime.getRuntime().
		exec(new String[]{ ICS_COMMAND, file.getPath() });

	    InputStream in = p.getInputStream();

	    String response = read(in);
	    in.close();

	    file.delete();

    
            // read the output from the command
	    logger.info("Here is what ICS has to say:\n");
	    logger.info(response);

	    //This part is responsible for logging
	    String logdir = System.getProperty("key.ics.logdir");
	    if (logdir == null || logdir.trim().length() == 0) {
		logger.warn("$KEY_ICS_LOG_DIR is empty or non-existent. Logging (of proofs, not with log4j) of ICS disabled.");
	    } else {
		try {
		    String logFileName = "ics-log_" + 
			getCurrentDateString() + ".log";
		    PrintWriter logfile = new PrintWriter
			(new BufferedWriter(new FileWriter
					    (new File(logdir, logFileName))));
		    LogicPrinter sp = new LogicPrinter
			(new ProgramPrinter(logfile), 
			 NotationInfo.createInstance(),
			 services);
		    sp.printSequent(goal.sequent());
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
	    //System.out.println(response.indexOf(":unsat"));
	    if (response.indexOf(":unsat") > -1) {
		logger.info("ICS has decided and found the negated formula to be unsatisfiable.");
		return new DecisionProcedureResult(true, response, Constraint.BOTTOM);
	    } else {
		logger.info("ICS has decided and found the negated formula to be satisfiable.");
		return new DecisionProcedureResult(false, "", Constraint.BOTTOM);
	    }
	    //constraintSet.chosenConstraint
	} catch (IOException ioe) {
	    final String errorMessage="\"ICS\" execution failed:\n\n"+
		 ioe+"\n\n"+
		 "To make use of ICS make sure that\n\n"+
		 "1. the binary is named ics\n"+
		 "2. the directory where the binary "+
		 "resides is in your $PATH variable\n"+
		 "3. the binary has executable file permissions.";
	    throw new RuntimeException(errorMessage);
	} catch (SimplifyException se) {
	    return new DecisionProcedureResult(false, se.toString(), 
	            Constraint.BOTTOM);
	}	
    }

}
