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

import de.uka.ilkd.key.java.ConvertException;
import antlr.Token;

public class JavaParserException extends antlr.SemanticException {
    
    String cat;
    String filename;
    String jb;

    public JavaParserException(String cat, Token t, String filename, 
			       int lineOffset, int colOffset) {
	super("JavaParser");
	this.cat      = cat;
	this.jb =t.getText();
	this.filename = filename;
	this.line = (lineOffset>=0) ? t.getLine()+lineOffset : 0;	
	this.column = (colOffset>=0) ? t.getColumn()+colOffset : 0;
    }
    
    public JavaParserException(Throwable e, Token t, String filename, 
               int lineOffset, int colOffset) {
        this(e.getMessage(), t, filename, lineOffset, colOffset);
        initCause(e);
    }
    

    public JavaParserException(String cat, Token t, String filename) {
	super("JavaParser");
	this.cat      = cat;
	this.jb  = t.getText();
	this.filename = filename;
	this.line     = t.getLine();
	this.column   = t.getColumn();

    }

    public JavaParserException(String message){
	super(message);
    }

    public JavaParserException(Throwable e, Token t, String filename) {
        this(e.getMessage(), t, filename);
        initCause(e);
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
