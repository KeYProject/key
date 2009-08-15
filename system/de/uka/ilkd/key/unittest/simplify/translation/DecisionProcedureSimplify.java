// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest.simplify.translation;

import java.io.*;
import java.util.Calendar;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;

/**
 * This class invokes the decision procedure "Simplify" which is part of
 * ESC/Java by Compaq.
 */

public class DecisionProcedureSimplify {

    private static final String SIMPLIFY_COMMAND = "Simplify";

    private static final String SPACER = "\\<---This is just a spacer between "
	    + "sequent and Simplify input resp. Simplify output--->\\";

    private final Constraint userConstraint;

    private final Services services;

    private final Node node;

    static Logger logger = Logger.getLogger(DecisionProcedureSimplify.class
	    .getName());

    public DecisionProcedureSimplify(Node node, Constraint userConstraint,
	    Services services) {
	this.node = node;
	this.userConstraint = userConstraint;
	this.services = services;
    }

    public static String execute(String input) throws IOException {
	File file = File.createTempFile("key-simplify", null);
	PrintWriter out = new PrintWriter(new FileWriter(file));
	out.println(input.replace('\n', ' '));
	out.close();

	Process p = Runtime.getRuntime().exec(
		new String[] { SIMPLIFY_COMMAND, file.getPath() });
	InputStream in = p.getInputStream();

	String response = read(in);
	in.close();

	file.delete();

	return response;
    }

    /**
     * the method responsible for making various calls to the underlying
     * decision procedure with different Constraints
     * 
     * @param lightWeight
     *            true iff only quantifier free formulas shall be considered.
     */
    public DecisionProcedureResult run(boolean lightWeight) {
	ConstraintSet constraintSet = new ConstraintSet(node.sequent(),
		userConstraint);
	constraintSet.chooseConstraintSet();
	DecisionProcedureResult res = runInternal(constraintSet, lightWeight);
	if (res.getResult()) {
	    return res;
	} else {
	    if (constraintSet.addUserConstraint(userConstraint)) {
		return runInternal(constraintSet, lightWeight);
	    } else {
		return res;
	    }
	}

    }

    /**
     * Constructs a date for use in log filenames.
     */
    private String getCurrentDateString() {
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
     * Read the input until end of file and return contents in a single string
     * containing all line breaks.
     */
    private static String read(InputStream in) throws IOException {
	String lineSeparator = System.getProperty("line.separator");
	BufferedReader reader = new BufferedReader(new InputStreamReader(in));
	StringBuffer sb = new StringBuffer();
	String line;
	while ((line = reader.readLine()) != null) {
	    sb.append(line).append(lineSeparator);
	}
	return sb.toString();
    }

    /**
     * runs first the conversion into the Simplify syntax, and runs Simplify via
     * a temporary file.
     * 
     * @param lightWeight
     *            true iff only quantifier free formulas shall be considered.
     */
    private DecisionProcedureResult runInternal(ConstraintSet constraintSet,
	    boolean lightWeight) {
	try {
	    SimplifyTranslation st = new SimplifyTranslation(node.sequent(),
		    constraintSet, node.getRestrictedMetavariables(),
		    this.services, lightWeight);

	    String response = execute(st.getText());

	    // read the output from the command
	    logger.info("Here is what Simplify has to say:\n");
	    logger.info(response);

	    // This part is responsible for logging
	    String logdir = System.getProperty("key.simplify.logdir");
	    if (logdir == null || logdir.trim().length() == 0) {
		logger
			.warn("$KEY_SIMPLIFY_LOG_DIR is empty or non-existent. Logging (of proofs, not with log4j) of Simplify disabled.");
	    } else {
		try {
		    String logFileName = "simplify-log_"
			    + getCurrentDateString() + ".log";
		    PrintWriter logfile = new PrintWriter(new BufferedWriter(
			    new FileWriter(new File(logdir, logFileName))));
		    LogicPrinter sp = new LogicPrinter(new ProgramPrinter(
			    logfile), NotationInfo.createInstance(), services);
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
	    // End of logging part

	    if (response.indexOf("Valid.") > 0) {
		logger
			.info("Simplify has decided and found the formula to be valid.");
		return new DecisionProcedureResult(true, response, st);
	    } else {
		return new DecisionProcedureResult(false, response, st);
	    }
	} catch (IOException ioe) {
	    final String errorMessage = "\"Simplify\" execution failed:\n\n"
		    + ioe
		    + "\n\n"
		    + "To make use of Simplify make sure that\n\n"
		    + "1. the binary is named Simplify (Linux) or "
		    + "Simplify.exe (Windows)\n"
		    + "2. the directory where the binary resides is in "
		    + "your $PATH variable\n"
		    + "3. the binary has executable file permissions (Linux only).";
	    throw new RuntimeException(errorMessage);
	} catch (SimplifyException se) {
	    return new DecisionProcedureResult(false, se.toString());
	}
    }

    private String toStringLeadingZeros(int n, int width) {
	String rv = "" + n;
	while (rv.length() < width) {
	    rv = "0" + rv;
	}
	return rv;
    }

}
