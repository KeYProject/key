// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.io.File;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.AbstractSMTTranslator.Configuration;

public interface SolverType {

    public SMTSolver createSolver(SMTProblem problem, SolverListener listener,
	    Services services);

    public String getName();

    public boolean isInstalled(boolean recheck);

    public void useTaclets(boolean b);

    public SMTSolverResult interpretAnswer(String text, String error, int val);

    public String getInfo();
    


    /**
     * Get the command for executing the external prover. This is a hardcoded
     * default value. It might be overridden by user settings
     * 
     * @param filename
     *            the location, where the file is stored.
     * @param formula
     *            the formula, that was created by the translator
     * @return Array of Strings, that can be used for executing an external
     *         decider.
     */
    public String getExecutionCommand(String filename, String formula);

    public String getExecutionCommand();

    public void setExecutionCommand(String s);

    public String getDefaultExecutionCommand();

    public SMTTranslator getTranslator(Services services);

    static public final SolverType Z3_SOLVER = new AbstractSolverType() {

	@Override
	public String getExecutionCommand(String filename, String formula) {
	    return "z3 -smt -m " + filename;
	}

	@Override
	public SMTSolver createSolver(SMTProblem problem,
	        SolverListener listener, Services services) {
	    return new SMTSolverImplementation(problem, listener, services,
		    this);
	}

	@Override
	public String getName() {
	    return "Z3";
	}

	@Override
	public SMTTranslator getTranslator(Services services) {
	    return new SmtLibTranslator(services,new Configuration(false));
	}

	public SMTSolverResult interpretAnswer(String text, String error,
	        int val) {
	    if (val == 0) {
		// no error occured
		if (text.contains("unsat")) {
		    return SMTSolverResult.createValidResult(text, getName());
		} else if (text.contains("sat")) {
		    return SMTSolverResult.createInvalidResult(text, getName());
		} else {
		    return SMTSolverResult.createUnknownResult(text, getName());
		}
	    } else if ((val == 112 && text.contains("unknown")) || val == 139) {
		// the result was unknown
		return SMTSolverResult.createUnknownResult(text, getName());
	    } else {
		// something went wrong
		throw new IllegalResultException("Code " + val + ": " + error);
	    }
	}

	@Override
	public String getInfo() {

	    return "Z3 does not use quantifier elimination by default. This means for example that"
		    + " the following problem cannot be solved automatically by default:\n\n"
		    + "\\functions{\n"
		    + "\tint n;\n"
		    + "}\n\n"
		    + "\\problem{\n"
		    + "\t((\\forall int x;(x<=0 | x >= n+1)) & n >= 1)->false\n"
		    + "}"
		    + "\n\n"
		    + "You can activate quantifier elimination by appending QUANT_FM=true to"
		    + " the execution command.";
	}
	

	

    };
    static public final SolverType CVC3_SOLVER = new AbstractSolverType() {

	@Override
	public String getName() {
	    return "CVC3";
	}

	@Override
	public SMTSolver createSolver(SMTProblem problem,
	        SolverListener listener, Services services) {
	    return new SMTSolverImplementation(problem, listener, services,
		    this);
	}

	@Override
	public String getExecutionCommand(String filename, String formula) {
	    return "cvc3 -lang smt +model " + filename;
	}

	@Override
	public SMTTranslator getTranslator(Services services) {
	    return new SmtLibTranslator(services,new Configuration(false));
	}

	@Override
	public String getInfo() {
	    return null;
	}

	@Override
	public SMTSolverResult interpretAnswer(String text, String error,
	        int val) {
	    if (val == 0) {
		// normal termination, no error
		if (text.startsWith("unsat\n")) {
		    return SMTSolverResult.createValidResult(text, getName());
		} else if (text.startsWith("sat\n")) {
		    return SMTSolverResult.createInvalidResult(text, getName());
		} else {
		    return SMTSolverResult.createUnknownResult(text, getName());
		}
	    } else {
		// error termination
		throw new IllegalResultException(error);
	    }
	}

    };
    static public final SolverType YICES_SOLVER = new AbstractSolverType() {

	@Override
	public String getName() {
	    return "Yices";
	}

	@Override
	public SMTSolver createSolver(SMTProblem problem,
	        SolverListener listener, Services services) {
	    return new SMTSolverImplementation(problem, listener, services,
		    this);
	}

	@Override
	public SMTTranslator getTranslator(Services services) {
	    return new SmtLibTranslator(services,new Configuration(true));
	}

	@Override
	public String getExecutionCommand(String filename, String formula) {
	    return "yices -tc -e -smt " + filename;
	}

	@Override
	public String getInfo() {
	    return "Use the newest release of version 1.x instead of version 2. Yices 2 does not support the "
		    + "required logic AUFLIA.";
	}

	@Override
	public SMTSolverResult interpretAnswer(String text, String error,
	        int val) {
	    if (val == 0) {
		if (text.startsWith("unsat\n")) {
		    return SMTSolverResult.createValidResult(text, getName());
		} else if (text.startsWith("sat\n")) {
		    return SMTSolverResult.createInvalidResult(text, getName());
		} else {
		    return SMTSolverResult.createUnknownResult(text, getName());
		}

	    } else {
		throw new IllegalResultException(error);
	    }

	}
	

    };
    static public final SolverType SIMPLIFY_SOLVER = new AbstractSolverType() {

	@Override
	public String getName() {
	    return "Simplify";
	}

	@Override
	public SMTSolver createSolver(SMTProblem problem,
	        SolverListener listener, Services services) {
	    return new SMTSolverImplementation(problem, listener, services,
		    this);
	}

	@Override
	public SMTTranslator getTranslator(Services services) {
	    return new SimplifyTranslator(services, new Configuration(false));
	}

	@Override
	public String getExecutionCommand(String filename, String formula) {
	    return "simplify " + filename;
	}

	@Override
	public String getInfo() {
	    return "Simplify only supports integers within the interval [-2147483646,2147483646]=[-2^31+2,2^31-2].";
	}
	

	@Override
	public SMTSolverResult interpretAnswer(String text, String error,
	        int val) {
	    if (val == 0) {
		// no error occured
		if (meansValid(text)) {
		    return SMTSolverResult.createValidResult(text, getName());
		} else if (meansInvalid(text)) {
		    return SMTSolverResult.createInvalidResult(text, getName());
		} else if (meansBadInput(text)) {
		    throw new IllegalResultException(text);

		} else {
		    return SMTSolverResult.createUnknownResult(text, getName());
		}
	    } else {
		// error occured
		throw new IllegalResultException(error);
	    }

	}

	private boolean meansBadInput(String text) {
	    return text.indexOf("Bad input") >= 0;
	}

	private boolean meansValid(String text) {
	    boolean toReturn = false;
	    String wanted = "Valid.";
	    int pos = text.indexOf(wanted);
	    if (pos != -1) {
		// Valid. is found. check, if it is on the end of the String and
		// if only \n are following
		toReturn = true;
		pos = pos + wanted.length();
		for (int i = pos + 1; i < text.length(); i++) {
		    if (text.charAt(i) != '\n' && text.charAt(i) != ' ') {
			toReturn = false;
		    }
		}
	    }
	    return toReturn;
	}

	private boolean meansInvalid(String text) {
	    boolean toReturn = false;
	    String wanted = "Invalid.";
	    int pos = text.indexOf(wanted);
	    if (pos != -1) {
		// Valid. is found. check, if it is on the end of the String and
		// if only \n are following
		toReturn = true;
		pos = pos + wanted.length();
		for (int i = pos + 1; i < text.length(); i++) {
		    if (text.charAt(i) != '\n' && text.charAt(i) != ' ') {
			toReturn = false;
		    }
		}
	    }
	    return toReturn;
	}
    };

}

abstract class AbstractSolverType implements SolverType {
    private boolean installWasChecked = false;
    private boolean isInstalled = false;
    private String executionCommand = getDefaultExecutionCommand();

    public static boolean isInstalled(String cmd) {

	int first = cmd.indexOf(" ");
	if (first >= 0) {
	    cmd = cmd.substring(0, first);
	}

	if (checkEnvVariable(cmd)) {
	    return true;
	} else {

	    File file = new File(cmd);

	    return file.exists();

	}
    }

    @Override
    public void useTaclets(boolean b) {

    }

    /**
     * check, if this solver is installed and can be used.
     * 
     * @param recheck
     *            if false, the solver is not checked again, if a cached value
     *            for this exists.
     * @return true, if it is installed.
     */
    public boolean isInstalled(boolean recheck) {
	if (recheck || !installWasChecked) {

	    String cmd = getExecutionCommand();
	    isInstalled = isInstalled(cmd);
	    if (isInstalled) {
		installWasChecked = true;
	    }

	}
	return isInstalled;
    }

    private static boolean checkEnvVariable(String cmd) {
	String filesep = System.getProperty("file.separator");
	String path = System.getenv("PATH");
	String[] res = path.split(System.getProperty("path.separator"));
	for (String s : res) {
	    File file = new File(s + filesep + cmd);
	    if (file.exists()) {
		return true;
	    }
	}

	return false;

    }

    /**
     * get the hard coded execution command from this solver. The filename od a
     * problem is indicated by %f, the problem itsself with %p
     */
    @Override
    public String getDefaultExecutionCommand() {
	return this.getExecutionCommand("%f", "%p");
    }

    public String getExecutionCommand() {
	return executionCommand;
    }

    public void setExecutionCommand(String s) {

	executionCommand = s;
    }

    public String toString() {
	return getName();
    }
    

}
