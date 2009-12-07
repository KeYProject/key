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


public final class YicesSolver extends AbstractSMTSolver {

    public static final String name = "Yices";
    

    public String name() {
	return name;
    }
    
    
    public SMTTranslator getTranslator(Services services) {
	return new SmtLibTranslator(services);
    }


    @Override
    protected String getExecutionCommand(String filename, String formula) {

	//String toReturn = "yices -tc -smt " + filename;
	//The following command tells yices to return a model if possible 
	String toReturn = "yices -tc -e -smt " + filename;

	return toReturn;
    }

    
    public SMTSolverResult interpretAnswer(String input, String error, int val) {
	if (val == 0) {
	    //no error occured
	    //The commented out code works if no models (counterexamples) interpreted
//	    if (input.equals("unsat\n")) {
//		return SMTSolverResult.createValidResult(input);
//	    } else if (input.equals("sat\n")) {
//		return SMTSolverResult.createInvalidResult(input);
//	    } else {
//		return SMTSolverResult.createUnknownResult(input);
//	    }
	    if (input.startsWith("unsat\n")) {
		return SMTSolverResult.createValidResult(input,name());
	    } else if (input.startsWith("sat\n")) {
		return SMTSolverResult.createInvalidResult(input,name());
	    } else {
		return SMTSolverResult.createUnknownResult(input,name());
	    }

	} else {
	    throw new IllegalArgumentException(error);
	}
	
	
    }
}
