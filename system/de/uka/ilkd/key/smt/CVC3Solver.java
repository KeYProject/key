// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt;


public class CVC3Solver extends AbstractSMTSolver {

    public static final String name= "CVC3";
    
    public String name() {
	return name;
    }
    
    



    
    @Override
    public String getDefaultCommand() {
        
        return "cvc3";
    }
    
    @Override
    public String getDefaultParameters() {
        return " -lang smt +model %f";
    }
    

    

    public SMTSolverResult interpretAnswer(String text, String error, int val) {
	if (val == 0) {
	    //normal termination, no error
	    if (text.startsWith("unsat\n")) {
		return SMTSolverResult.createValid(text,name());
	    } else if (text.startsWith("sat\n")) {
		return SMTSolverResult.createInvalid(text,name());
	    } else {
		return SMTSolverResult.createUnknown(text,name());
	    }
	} else {
	    //error termination
	    throw new IllegalArgumentException(error);
	}
	
    }
}
