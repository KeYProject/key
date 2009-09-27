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
    protected String getExecutionCommand(String filename, String formula) {
	//String toReturn = new String[4];

	String toReturn = "cvc3 -lang smt " + filename;
	//toReturn[1] = "-lang";
	//toReturn[2] = "smt";
	//toReturn[3] = filename;

	return toReturn;
    }

    

    public SMTSolverResult interpretAnswer(String text, String error, int val) {
	if (val == 0) {
	    //normal termination, no error
	    if (text.equals("unsat\n")) {
		return SMTSolverResult.createValidResult(text);
	    } else if (text.equals("sat\n")) {
		return SMTSolverResult.createInvalidResult(text);
	    } else {
		return SMTSolverResult.createUnknownResult(text);
	    }
	} else {
	    //error termination
	    throw new IllegalArgumentException(error);
	}
	
    }
}
