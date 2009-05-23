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

    public String name() {
	return "Yices";
    }
    
    
    public SMTTranslator getTranslator(Services services) {
	return new SmtLibTranslator(services);
    }


    @Override
    protected String[] getExecutionCommand(String filename, String formula) {
	String[] toReturn = new String[4];

	toReturn[0] = "yices";
	toReturn[1] = "-tc";
	toReturn[2] = "-smt";
	toReturn[3] = filename;

	return toReturn;
    }

    
    @Override
    protected SMTSolverResult interpretAnswer(String input, String error, int val) {
	if (val == 0) {
	    //no error occured
	    if (input.equals("unsat\n")) {
		return SMTSolverResult.createValidResult(input);
	    } else if (input.equals("sat\n")) {
		return SMTSolverResult.createInvalidResult(input);
	    } else {
		return SMTSolverResult.createUnknownResult(input);
	    }
	} else {
	    throw new IllegalArgumentException(error);
	}
	
	
    }
}
