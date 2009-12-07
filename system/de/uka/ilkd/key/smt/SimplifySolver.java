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


public final class SimplifySolver extends AbstractSMTSolver {
    
    public static final String name="Simplify";

    public String name() {
        return name;
    }
    
    
    public SMTTranslator getTranslator(Services services) {
	return new SimplifyTranslator(services);
    }
    
    @Override
    protected String getExecutionCommand(String filename, String formula) {

	String toReturn = "simplify " + filename;

	return toReturn;
    }

    

    public SMTSolverResult interpretAnswer(String text, String error, int val) {	
	
	if (val == 0) {
	    //no error occured
	    if (meansValid(text)) {
		return SMTSolverResult.createValidResult(text,name());
	    } else if (meansInvalid(text)) {
		return SMTSolverResult.createInvalidResult(text,name());
	    } else {
		return SMTSolverResult.createUnknownResult(text,name());
	    } 
	} else {
	    //error occured
	    throw new IllegalArgumentException(error);
	}
	
    }    
    
    private boolean meansValid(String text) {
	boolean toReturn = false;
	String wanted = "Valid.";
	int pos = text.indexOf(wanted);
	if (pos != -1) {
	    //Valid. is found. check, if it is on the end of the String and if only \n are following
	    toReturn = true;
	    pos = pos + wanted.length();
	    for (int i = pos + 1; i < text.length(); i++) {
		if (text.charAt(i) != '\n'
		    && text.charAt(i) != ' ') {
		    toReturn = false;
		}
	    }
	}
	return toReturn;
    }
    
    private boolean meansInvalid(String text) {
	boolean toReturn = false;
	String wanted = "Invalid.";
	int pos = text.indexOf(wanted);
	if (pos != -1) {
	    //Valid. is found. check, if it is on the end of the String and if only \n are following
	    toReturn = true;
	    pos = pos + wanted.length();
	    for (int i = pos + 1; i < text.length(); i++) {
		if (text.charAt(i) != '\n'
		    && text.charAt(i) != ' ') {
		    toReturn = false;
		}
	    }
	}
	return toReturn;
    }
    
}
