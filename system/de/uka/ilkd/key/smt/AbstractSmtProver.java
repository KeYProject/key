package de.uka.ilkd.key.smt;

import java.io.*;
import java.util.Calendar;
import java.util.Date;
import java.util.Timer;

import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import org.apache.log4j.Logger;

public abstract class AbstractSmtProver {

    //public static final int VALID = 0;

    //public static final int INVALID = 1;

    //public static final int UNKNOWN = 2;

    public static enum RESULTTYPE {VALID, INVALID, UNKNOWN};
    
    private static final Logger logger = Logger
	    .getLogger(AbstractSmtProver.class.getName());

    /**
     * The path for the file
     */
    private static final String fileDir = PathConfig.KEY_CONFIG_DIR
	    + File.separator + "smt_formula";

    /**
     * This rule's name.
     */
    public abstract String displayName();

    /**
     * This rule's name as Name object.
     */
    public abstract Name name();

    protected boolean isApplicable(Goal goal) {
	boolean toReturn = true;
	Semisequent ant = goal.sequent().antecedent();
	for (ConstrainedFormula c : ant) {
	    toReturn = toReturn && this.isApplicable(c.formula());
	}
	
	Semisequent succ = goal.sequent().succedent();
	for (ConstrainedFormula c : succ) {
	    toReturn = toReturn && this.isApplicable(c.formula());
	}
	
	return toReturn;
    }
    
    /**
     * TODO overwork
     */
    protected boolean isApplicable(Term term) {
	
	Operator op = term.op();
	if (op == Op.NOT) {
	    return isApplicable(term.sub(0));
	} else if (op == Op.AND) {
	    return (isApplicable(term.sub(0)) && isApplicable(term.sub(1)));
	} else if (op == Op.OR) {
	    return (isApplicable(term.sub(0)) && isApplicable(term.sub(1)));
	} else if (op == Op.IMP) {
	    return (isApplicable(term.sub(0)) && isApplicable(term.sub(1)));
	} else if (op == Op.EQV) {
	    return (isApplicable(term.sub(0)) && isApplicable(term.sub(1)));
	} else if (op == Op.EQUALS) {
	    return (isApplicable(term.sub(0)) && isApplicable(term.sub(1)));

	} else if (op == Op.ALL) {
	    return isApplicable(term.sub(0));
	} else if (op == Op.EX) {
	    return isApplicable(term.sub(0));
	} else if (op == Op.TRUE) {
	    return true;
	} else if (op == Op.FALSE) {
	    return true;
	} else if (op == Op.NULL) {
	    return true;
	} else if (op instanceof LogicVariable || op instanceof ProgramVariable) {
	    // translate as variable or constant
	    return true;
	} else if (op instanceof Function) {
	    boolean temp = true;
	    for (int i = 0; i < term.arity(); i++) {
		temp = temp && this.isApplicable(term.sub(i));
	    }
	    return temp;
	} else if (op instanceof ArrayOp) {
	    boolean temp = true;
	    ArrayOp operation = (ArrayOp) op;
	    temp = temp && this.isApplicable(operation.referencePrefix(term));
	    temp = temp && this.isApplicable(operation.index(term));
	    return temp;
	} else if (op instanceof AttributeOp) {
	    AttributeOp atop = (AttributeOp) op;
	    boolean temp = true;
	    for (int i = 0; i < atop.arity(); i++) {
		temp = temp && isApplicable(term.sub(i));
	    }
	    return temp;
	} else {
	    return false;
	}
	
    }

    /**
     * Get the abstract translator, that should be used to
     * @return the translator, that should be used.
     */
    protected abstract AbstractSmtTranslator getTranslator(Goal goal,
	    Services services, RuleApp ruleApp);

    /**
     * Get the command for executing an external proofer.
     * @param filename the location, where the file is stored.
     * @param formula the formula, that was created by the translator
     * @return Array of Strings, that can be used for executing an external decider.
     */
    protected abstract String[] getExecutionCommand(String filename,
	    StringBuffer formula);

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
    private final String storeToFile(StringBuffer text) throws IOException {
	String loc = fileDir + getCurrentDateString();
	new File(fileDir).mkdirs();
	BufferedWriter out = new BufferedWriter(new FileWriter(loc));
	out.write(text.toString());
	out.close();

	return loc;
    }

    /**
     * 
     * @param answer the String answered by the external programm
     * @return VALID, if the formula was proven valid, 
     *      INVALID, if the formula was proven invalid,
     *      UNKNOWN, if the formula could not be proved
     */
    protected abstract RESULTTYPE answerType(String answer);

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
     * Check, if the formula in the goal is valid.
     * @param goal The goal to be proven.
     * @param timeout The maximum time, that should be used to execute the external solver.
     *      Given in seconds. If the time is exceeded, UNKNOWN is returned.
     * @param services The service object wrapping different settings and variables.
     * @param ruleApp The Rule Application
     * @return VALID, INVALID or UNKNOWN.
     */
    public final RESULTTYPE isValid(Goal goal, int timeout, Services services,
	    RuleApp ruleApp) {
	RESULTTYPE toReturn = RESULTTYPE.UNKNOWN;

	if (!this.isApplicable(goal)) {
	    return RESULTTYPE.UNKNOWN;
	}
	
	try {
	    //get the translation
	    AbstractSmtTranslator trans = this.getTranslator(goal, services,
		    ruleApp);
	    String loc;

	    try {
		StringBuffer s = trans.translate(goal.sequent(), services);
		//store the translation to a file                                
		loc = this.storeToFile(s);
		//get the commands for execution
		String[] execCommand = this.getExecutionCommand(loc, s);

		try {

		    Process p = Runtime.getRuntime().exec(execCommand);
		    ExecutionWatchDog tt = new ExecutionWatchDog(timeout, p);
		    Timer t = new Timer();
		    t.schedule(tt, new Date(System.currentTimeMillis()), 1000);
		    try {
			p.waitFor();
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
			toReturn = RESULTTYPE.UNKNOWN;
		    } else {
			//the process terminated as it sould
			InputStream in = p.getInputStream();
			String result = read(in);
   
			logger.debug("Answer for created formula: ");
			logger.debug(result);
			in.close();
			RESULTTYPE validity = this.answerType(result);
			if (validity == RESULTTYPE.VALID) {
			    toReturn = RESULTTYPE.VALID;
			} else if (validity == RESULTTYPE.INVALID) {
			    toReturn = RESULTTYPE.INVALID;
			} else {
			    toReturn = RESULTTYPE.UNKNOWN;
			}
		    }
		} catch (IOException e) {
		    logger
			    .error(
				    "The program for proving a Formula with external tool could not be executed.",
				    e);
		} finally {
		    //remove the created file
		    File f = new File(loc);
		    f.delete();
		}
	    } catch (IOException e) {
		logger.error("The file with the formula could not be written.",
			e);
	    }
	} catch (IllegalFormulaException e) {
	    toReturn = RESULTTYPE.UNKNOWN;
	    logger.error("The formula could not be translated.", e);
	}
	return toReturn;
    }

}
