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


package de.uka.ilkd.key.speclang.translation;    

import antlr.ANTLRException;
import antlr.LLkParser;
import antlr.RecognitionException;
import antlr.Token;
import antlr.TokenStreamException;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.jml.pretranslation.KeYJMLPreParser;


/**
 * Some common exception / position management functionality used 
 * by SL translation parsers.
 */
public class SLTranslationExceptionManager {
    
    private final String fileName;
    private final Position offsetPos;
    private final int line;
    private final int column;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public SLTranslationExceptionManager(LLkParser parser, 
                                         String fileName, 
                                         Position offsetPos) {
	int line;
	int column;
	try {
	    line = parser.LT(1).getLine();
	    column = parser.LT(1).getColumn();
	} catch (final TokenStreamException e) {
	    line = 1;
	    column = 1;
	}

	this.line = line;
	this.column = column;
	this.fileName = fileName;
	this.offsetPos = offsetPos;
    }

    public SLTranslationExceptionManager(KeYJMLPreParser parser,
                                         String fileName,
                                         Position offsetPos) {
        this.line = parser.input.LT(1).getLine();
        this.column = parser.input.LT(1).getCharPositionInLine();
        this.fileName  = fileName;
        this.offsetPos = offsetPos;
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private Position createAbsolutePosition(int relativeLine, 
                                            int relativeColumn) {
        int absoluteLine = offsetPos.getLine() + relativeLine - 1;
        int absoluteColumn = (relativeLine == 1 ? offsetPos.getColumn() : 1) 
                             + relativeColumn - 1;
        return new Position(absoluteLine, absoluteColumn); 
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
        
    /**
     * Creates a string with the position information of the passed token.
     */
    public PositionedString createPositionedString(String text, Token t) {
        return new PositionedString(text, 
                                    fileName, 
                                    createAbsolutePosition(t.getLine(), 
                                                           t.getColumn()));
    }   
    
    public PositionedString createPositionedString(String text,
	    org.antlr.runtime.Token t) {
	return new PositionedString(text, fileName, createAbsolutePosition(
		t.getLine(), t.getCharPositionInLine()));
    }
    
    /**
     * Creates a string with the current absolute position information
     */
    public PositionedString createPositionedString(String text) {
        return new PositionedString(text, 
                                    fileName, 
                                    createAbsolutePosition(this.line, this.column));
    }
    
    
    /**
     * Creates an SLTranslationException with current absolute position 
     * information.
     */
    public SLTranslationException createException(String message) {
        return new SLTranslationException(message, 
                                          fileName, 
                                          createAbsolutePosition(this.line, this.column));
    }
            
    
    /**
     * Creates an SLTranslationException with the position information of the
     * passed token.
     */
    public SLTranslationException createException(String message, Token t) {
        return new SLTranslationException(message,
                                          fileName,
                                          createAbsolutePosition(t.getLine(),
                                                                 t.getColumn()));
    }

    public SLTranslationException createException(String message,
	    org.antlr.runtime.Token t) {
	return new SLTranslationException(message, fileName,
		createAbsolutePosition(t.getLine(), t.getCharPositionInLine()));
    }

    /**
     * Creates an SLTranslationException with current absolute position 
     * information.
     */
    public SLTranslationException createException(String message, Throwable cause){
        SLTranslationException result = createException(message);
        result.initCause(cause);
        return result;
    }
    
    /**
     * Creates an SLTranslationException with the position information of the
     * passed token.
     * 
     * @param cause the exception which causes the new exception to be created.
     */
    public SLTranslationException createException(String message, Token t, Throwable cause) {
        SLTranslationException result = createException(message, t);
        result.initCause(cause);
        return result;
    }
    
    
    /**
     * Creates an SLWarningException with current absolute position 
     * information.
     */
    public SLTranslationException createWarningException(String message) {
        return new SLWarningException(message, 
                                      fileName, 
                                      createAbsolutePosition(this.line, this.column));
    }
    
    public SLTranslationException createWarningException(String message, Token t) {
        return new SLWarningException(new PositionedString(message, t));
    }
    
    public SLTranslationException createWarningException(String message,
	    org.antlr.runtime.Token t) {
	return new SLWarningException(new PositionedString(message, t));
    }

    /**
     * Converts an ANTLRException into an SLTranslationException with the same
     * message and stack trace, and with current absolute position information.
     */
    public SLTranslationException convertException(ANTLRException e) {
        Position pos;
        if(e instanceof RecognitionException) {
            RecognitionException re = (RecognitionException) e;
            pos = createAbsolutePosition(re.getLine(), re.getColumn());
        } else {
            pos = createAbsolutePosition(this.line, this.column);
        }
        
        return new SLTranslationException(e.getMessage() 
                                          + " (" 
                                          + e.getClass().getName() 
                                          + ")", 
                                          fileName, 
                                          pos,
                                          e.getStackTrace());
    }

    public SLTranslationException convertException(
	    org.antlr.runtime.RecognitionException e) {
	Position pos;
	pos = createAbsolutePosition(e.line, e.charPositionInLine);

	return new SLTranslationException(e.getMessage() + " ("
		+ e.getClass().getName() + ")", fileName, pos,
		e.getStackTrace());
    }
}
