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

import antlr.Token;

public class AmbigiousDeclException extends antlr.SemanticException {
    /**
     * 
     */
    private static final long serialVersionUID = 5836342271644427009L;
    String filename = "unknown";
    String ambigious_symbol;
    Token t;
    
    public AmbigiousDeclException(String cat, Token t) {
	super("Name already in use");
	this.ambigious_symbol = t.getText();
	this.filename = t.getFilename();
	this.line     = t.getLine();
	this.column   = t.getColumn();
    }

    public AmbigiousDeclException(String ambigious_symbol, 
				  String filename, 
				  int line, 
				  int column) {
	super("Name already in use");
	this.filename = filename;
	this.ambigious_symbol = ambigious_symbol;
	this.line   = line;
	this.column = column;
    }
    /**
     * Returns a clean error message (no line number/column information)
     * @deprecated
     */
    @Deprecated
    public String getErrorMessage () {
	return getMessage();
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getMessage ()
    {
	return "The name \'" + ambigious_symbol + "\' is already in use.";
    }
    
    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return filename + "("+this.getLine()+", "+this.getColumn()+"):\n"
	    + getMessage();
    }
}
