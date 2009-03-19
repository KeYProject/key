package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;


public class YicesSmtSolver extends AbstractSmtSolver {

    public String name() {
	return "Yices";
    }

    /**
     * Set the abstract translator, that should be used to
     * 
     * @return the translator, that should be used.
     */
    protected AbstractSmtTranslator getTranslator(Services services) {
	return new SmtLibTranslator(services);
    }

    /**
     * Get the command for executing an external proofer.
     * 
     * @param filename
     *                the location, where the file is stored.
     * @param formula
     *                the formula, that was created by the translator.
     * @return Array of Strings, that can be used for executing an external
     *         decider.
     */
    protected String[] getExecutionCommand(String filename, StringBuffer formula) {
	String[] toReturn = new String[4];

	toReturn[0] = "yices";
	toReturn[1] = "-tc";
	toReturn[2] = "-smt";
	toReturn[3] = filename;

	return toReturn;
    }

    /**
     * 
     * @param answer
     *                the String answered by the external programm
     * @return VALID, if the formula was proven valid, INVALID, if the
     *         formula was proven invalid, UNKNOWN, if the formula could not
     *         be proved
     */
    protected SmtSolver.RESULTTYPE answerType(String answer) {
	if (answer.equals("unsat\n")) {
	    return SmtSolver.RESULTTYPE.VALID;
	} else if (answer.equals("sat\n")) {
	    return SmtSolver.RESULTTYPE.INVALID;
	} else {
	    return SmtSolver.RESULTTYPE.UNKNOWN;
	}
    }
}
