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

class UnfittingReplacewithException 
    extends antlr.SemanticException {
    
    /**
     * 
     */
    private static final long serialVersionUID = -497885048593588941L;
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
