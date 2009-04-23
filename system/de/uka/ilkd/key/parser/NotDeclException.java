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

import antlr.Token;

public class NotDeclException extends antlr.SemanticException {
    String cat;
    String undeclared_symbol;
    String addtl;
    
    public NotDeclException(String cat, Token t, String filename) {
	super("NotDeclared");
	this.cat      = cat;
	this.fileName = filename;
	this.undeclared_symbol = t.getText();
	this.line     = t.getLine();
	this.column   = t.getColumn();
    }

    public NotDeclException(String cat, String undeclared_symbol, 
			    String filename, int line, int column, String addtl) {
	super("NotDeclared");
	this.fileName = filename;
	this.cat      = cat;
	this.undeclared_symbol = undeclared_symbol;
	this.line     = line;
	this.column   = column;
	this.addtl    = addtl;
    }

    public NotDeclException(String cat, String undeclared_symbol, 
		    String filename, int line, int column) {
    	this(cat, undeclared_symbol, filename, line, column, "");
    }
    
    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getErrorMessage ()
    {
	String errmsg = cat + "\n\t" + undeclared_symbol + "\n";
	return errmsg + "not declared "+addtl;
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getMessage () {
	return getErrorMessage();
    }
    
    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return getFilename()+"("+this.getLine()+", "+this.getColumn()+"): "
	    +getErrorMessage();
    }
}
