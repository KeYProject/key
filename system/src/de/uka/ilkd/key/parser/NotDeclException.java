// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;

import org.antlr.runtime.RecognitionException;

import antlr.Token;

public class NotDeclException extends RecognitionException {
    /**
     * 
     */
    private static final long serialVersionUID = -237567578063439448L;
    String cat;
    String undeclared_symbol;
    String addtl;
    private String fileName;
    
    public NotDeclException(String cat, Token t, String filename) {
	this.cat      = cat;
	this.fileName = filename;
	this.undeclared_symbol = t.getText();
	this.line     = t.getLine();
	this.charPositionInLine   = t.getColumn();
    }

    public NotDeclException(String cat, String undeclared_symbol, 
			    String filename, int line, int column, String addtl) {
	this.fileName = filename;
	this.cat      = cat;
	this.undeclared_symbol = undeclared_symbol;
	this.line     = line;
	this.charPositionInLine   = column;
	this.addtl    = addtl;
    }

    public NotDeclException(String cat, String undeclared_symbol, 
		    String filename, int line, int column) {
    	this(cat, undeclared_symbol, filename, line, column, "");
    }
    
    /**
     * Returns a clean error message (no line number/column information)
     * @deprecated
     */
    @Deprecated
    public String getErrorMessage ()
    {
	return getMessage();
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getMessage () {
	String errmsg = cat + "\n\t" + undeclared_symbol + "\n";
	return errmsg + "not declared "+addtl;
    }
    
    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return this.fileName+"("+this.line+", "+this.charPositionInLine+"): "
	    +getMessage();
    }
}