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

/**Hint: In order to run Z3 on Linux or Mac use wine. 
 * On {@link http://www4.in.tum.de/~boehmes/z3.html} you can find useful script for that. 
 * Please not that you have to run "winetricks vcrun2008". */
public final class Z3Solver extends AbstractSMTSolver {

    public static final String name="Z3";
    public String name() {
        return name;
    }
    
    
    
    @Override
    protected String getExecutionCommand(String filename, String formula) {

	//String toReturn = "z3 -smt " + filename;
	//The following is create a model if possible
	String toReturn = "z3 -smt -m " + filename;
	
	return toReturn;
    }
    
    
    public SMTSolverResult interpretAnswer(String text, String error, int val) {
	if (val == 0) {
	    //no error occured
	    if (text.contains("unsat")) {
		return SMTSolverResult.createValidResult(text,name());
	    } else if (text.contains("sat")) {
		return SMTSolverResult.createInvalidResult(text,name());
	    } else {
		return SMTSolverResult.createUnknownResult(text,name());
	    }
	} else if (val == 112 && text.contains("unknown")) {
	    //the result was unknown
	    return SMTSolverResult.createUnknownResult(text,name());
	} else {
	    //something went wrong
	    throw new IllegalArgumentException(error);
	}
    }
}
