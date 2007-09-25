// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.parser;

class InvalidFindException 
    extends antlr.SemanticException {
    
    private String description;
    
    public InvalidFindException(String description,
				String filename,
				int line, int column) {
	super("Invalid Find: "+description, filename, line, column);
	this.description = description;
    }
    
    public String getMessage() {
	return (getFilename() != null ? getFilename() : "") +
            "("+getLine()+", "+getColumn()+ "):" + description;	
    }		
    
}
