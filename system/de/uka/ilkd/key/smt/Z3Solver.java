// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.smt;


/**Hint: In order to run Z3 on Linux or Mac use wine. 
 * On {@link http://www4.in.tum.de/~boehmes/z3.html} you can find useful script for that. 
 * Please note that you have to run "winetricks vcrun2008". 
 */
public final class Z3Solver extends AbstractSMTSolver {

    public static final String name = "Z3";

    public String name() {
        return name;
    }
    
    
    

    
    @Override
    public String getDefaultCommand() {
        return "z3";
    }
    
    @Override
    public String getDefaultParameters() {
        return "-smt -m %f";
    }
    
    
    public SMTSolverResult interpretAnswer(String text, String error, int val) {
	if (val == 0) {
	    //no error occurred
	    if (text.contains("unsat")) {
		return SMTSolverResult.createValid(text,name());
	    } else if (text.contains("sat")) {
		return SMTSolverResult.createInvalid(text,name());
	    } else {
		return SMTSolverResult.createUnknown(text,name());
	    }
	} else if ((val == 112 && text.contains("unknown")) || val == 139) {
	    //the result was unknown
	    return SMTSolverResult.createUnknown(text, name());
	} else {
	    //something went wrong
	    throw new IllegalArgumentException("Code "+ val+": " + error);
	}
    }
    

    @Override
    public String getInfo() {
     
        return "Z3 does not use quantifier elimination by default. This means for example that" +
        	" the following problem cannot be solved automatically by default:\n\n"
        	+"\\functions{\n"+
        	 "\tint n;\n"+
         	 "}\n\n"+
                 "\\problem{\n"+
         	   "\t((\\forall int x;(x<=0 | x >= n+1)) & n >= 1)->false\n"+
    		 "}"+
    		 "\n\n"+
    		 "You can activate quantifier elimination by appending QUANT_FM=true to"+
    		 " the execution command."; 
    }
}
