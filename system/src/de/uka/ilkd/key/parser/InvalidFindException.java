// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.parser;

import org.antlr.runtime.RecognitionException;

public class InvalidFindException
    extends RecognitionException {
    
    /**
     * 
     */
    private static final long serialVersionUID = 1699188390606912785L;
    private String description;
    private String filename;
    
    public InvalidFindException(String description,
				String filename,
				int line, int column) {
	this.filename = filename;
	this.line = line;
	this.charPositionInLine = column;
	this.description = description;
    }
    
    public String getMessage() {
	return (this.filename != null ? this.filename : "") +
            "("+this.line+", "+this.charPositionInLine+ "):" + description;
    }		
    
}
