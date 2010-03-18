package de.uka.ilkd.key.smt;


public class CVC3Solver extends AbstractSMTSolver {

    public static final String name= "CVC3";
    
    public String name() {
	return name;
    }
    
    


    @Override
    protected String getExecutionCommand(String filename, String formula) {
	//String toReturn = new String[4];

//	String toReturn = "cvc3 -lang smt " + filename;
	String toReturn = "cvc3 -lang smt +model " + filename;

	return toReturn;
    }

    

    public SMTSolverResult interpretAnswer(String text, String error, int val) {
	if (val == 0) {
	    //normal termination, no error
	    if (text.startsWith("unsat\n")) {
		return SMTSolverResult.createValidResult(text,name());
	    } else if (text.startsWith("sat\n")) {
		return SMTSolverResult.createInvalidResult(text,name());
	    } else {
		return SMTSolverResult.createUnknownResult(text,name());
	    }
	} else {
	    //error termination
	    throw new IllegalArgumentException(error);
	}
	
    }
}
