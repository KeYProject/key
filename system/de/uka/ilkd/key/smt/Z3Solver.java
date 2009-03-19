package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;


public class Z3Solver extends AbstractSmtSolver {

    
    public String name() {
        return "Z3";
    }
    
    
    @Override
    protected SmtTranslator getTranslator(Services services) {
	return new SmtLibTranslator(services);
    }
    
    @Override
    protected String[] getExecutionCommand(String filename, StringBuffer formula) {
	String[] toReturn = new String[3];

	toReturn[0] = "z3";
	toReturn[1] = "-smt";
	toReturn[2] = filename;
	
	return toReturn;
    }
    
    @Override
    protected RESULTTYPE answerType(String answer) {
	if (answer.contains("unsat")) {
	    return SmtSolver.RESULTTYPE.VALID;
	} else if (answer.contains("sat")) {
	    return SmtSolver.RESULTTYPE.INVALID;
	} else {
	    return SmtSolver.RESULTTYPE.UNKNOWN;
	}
    }
    
}
