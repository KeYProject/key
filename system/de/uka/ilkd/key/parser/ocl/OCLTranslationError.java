// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.parser.ocl;

import de.uka.ilkd.key.speclang.SLTranslationError;

public class OCLTranslationError extends antlr.RecognitionException {

	String message = "";
	

	public OCLTranslationError(String msg) {
		super(msg);
        this.message = msg;
	}

    public OCLTranslationError(String msg, int line, int col) {
        super(msg, "", line, col);
        this.message = msg;
    }
	
    public String getMessage() {
		return this.message;
	}

    public SLTranslationError getSLTranslationError() {
	SLTranslationError result = new SLTranslationError(message, getLine(), getColumn());
    	result.setStackTrace(getStackTrace());
    	return result;
    }
}
