package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;

public class CVC3Solver extends AbstractSMTSolver {

    public String name() {
	return "CVC3";
    }
    
    
    public SMTTranslator getTranslator(Services services) {
	return new SmtLibTranslator(services);
    }


    @Override
    protected String[] getExecutionCommand(String filename, String formula) {
	String[] toReturn = new String[4];

	toReturn[0] = "cvc3";
	toReturn[1] = "-lang";
	toReturn[2] = "smt";
	toReturn[3] = filename;

	return toReturn;
    }

    
    @Override
    protected SMTSolverResult interpretAnswer(String text) {
	if (text.equals("unsat\n")) {
	    return SMTSolverResult.createValidResult(text);
	} else if (text.equals("sat\n")) {
	    return SMTSolverResult.createInvalidResult(text);
	} else {
	    return SMTSolverResult.createUnknownResult(text);
	}
    }
}
