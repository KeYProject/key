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
    
    public String name() {
        return "Simplify";
    }
    
    
    public SMTTranslator getTranslator(Services services) {
	return new SimplifyTranslator(services);
    }
    
    
    @Override
    protected String[] getExecutionCommand(String filename, String formula) {
	String[] toReturn = new String[2];

	toReturn[0] = "simplify";
	toReturn[1] = filename;

	return toReturn;
    }

    
    @Override
    protected SMTSolverResult interpretAnswer(String text) {
	if (meansValid(text)) {
	    return SMTSolverResult.createValidResult(text);
	} else if (meansInvalid(text)) {
	    return SMTSolverResult.createInvalidResult(text);
	} else {
	    return SMTSolverResult.createUnknownResult(text);
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
