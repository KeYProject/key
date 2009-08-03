//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;


public final class Z3Solver extends AbstractSMTSolver {

    public String name() {
        return "Z3";
    }
    
    
    public SMTTranslator getTranslator(Services services) {
	return new SmtLibTranslator(services);
    }
    
    
    @Override
    protected String getExecutionCommand(String filename, String formula) {
	//String[] toReturn = new String[3];

	String toReturn = "z3 -smt " + filename;
	//toReturn[1] = "-smt";
	//toReturn[2] = filename;
	
	return toReturn;
    }
    
    
    public SMTSolverResult interpretAnswer(String text, String error, int val) {
	if (val == 0) {
	    //no error occured
	    if (text.contains("unsat")) {
		return SMTSolverResult.createValidResult(text);
	    } else if (text.contains("sat")) {
		return SMTSolverResult.createInvalidResult(text);
	    } else {
		return SMTSolverResult.createUnknownResult(text);
	    }
	} else if (val == 112 && text.contains("unknown")) {
	    //the result was unknown
	    return SMTSolverResult.createUnknownResult(text);
	} else {
	    //something went wrong
	    throw new IllegalArgumentException(error);
	}
    }
}
