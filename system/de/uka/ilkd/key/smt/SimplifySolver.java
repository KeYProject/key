package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;


public class SimplifySolver extends AbstractSmtSolver {

    
    public String name() {
        return "Simplify";
    }
    
    @Override
    protected SmtTranslator getTranslator(Services services) {
	return new SimplifyTranslator(services);
    }
    
    
    @Override
    protected String[] getExecutionCommand(String filename, StringBuffer formula) {
	String[] toReturn = new String[2];

	toReturn[0] = "simplify";
	toReturn[1] = filename;

	return toReturn;
    }
    
    protected SmtSolver.RESULTTYPE answerType(String answer) {
	if (answer.indexOf("Valid") != -1) {
	    return SmtSolver.RESULTTYPE.VALID;
	} else if (answer.indexOf("Invalid") != -1) {
	    return SmtSolver.RESULTTYPE.INVALID;
	} else {
	    return SmtSolver.RESULTTYPE.UNKNOWN;
	}
    }
    
}
