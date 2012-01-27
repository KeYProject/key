// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt;


public final class YicesSolver extends AbstractSMTSolver {

    public static final String name = "Yices";
    

    public String name() {
	return name;
    }
    


    
    @Override
    public String getDefaultParameters() {
        return  "-tc -e -smt %f";
    }
    
    @Override
    public String getDefaultCommand() {
        return "yices";
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
		return SMTSolverResult.createValid(input,name());
	    } else if (input.startsWith("sat\n")) {
		return SMTSolverResult.createInvalid(input,name());
	    } else {
		return SMTSolverResult.createUnknown(input,name());
	    }

	} else {
	    throw new IllegalArgumentException(error);
	}
	
	
    }
    

    @Override
    public String getInfo() {
       return "Use the newest release of version 1.x instead of version 2. Yices 2 does not support the " +
       	       "required logic AUFLIA.";
    }
}
