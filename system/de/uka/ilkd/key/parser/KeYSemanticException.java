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

public class KeYSemanticException extends antlr.SemanticException {
    String cat;
    String filename;
    Token t;
    
    public KeYSemanticException(String cat, Token t, String filename) {
	super("Semantic Error", filename, t.getLine(), t.getColumn());
	this.cat      = cat;
	this.filename = filename;
	this.t = t;
	this.line     = t.getLine();
	this.column   = t.getColumn();    
    }

    public KeYSemanticException(String cat, String filename, int line, int column) {
	super("Semantic Error", filename, line, column);
	this.cat      = cat;
	this.filename = filename;
	this.line     = line;
	this.column   = column;
   }

    public KeYSemanticException(String cat, int line, int column, String file){
        this(cat, file, line, column);  
    }

    public KeYSemanticException(String message){
	super(message);    
    }

    public String getFilename() {
        return filename;
    }
    
    public int getLine() {
        return line;        
    }
    
    public int getColumn() {
        return column;
    }   

    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getErrorMessage ()
    {
	return cat;
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getMessage ()
    {
	return getErrorMessage();
    }
    
    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return filename+"("+this.getLine()+", "+this.getColumn()+"): "
	    +getErrorMessage();
    }
}
