// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.parser;

class UnfittingReplacewithException 
    extends antlr.SemanticException {
    
    private String description;
    
    public UnfittingReplacewithException(String description,
					 String filename,
					 int line , int column) {
	super("Unfitting Replacewith", filename, line, column);
	this.description = description;
    }
    

    public String getMessage() {
	return description;
    }			
    
}	
