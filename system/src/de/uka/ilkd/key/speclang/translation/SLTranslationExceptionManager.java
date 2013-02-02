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
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;


/**
 * Some common exception / position management functionality used 
 * by SL translation parsers.
 */
public class SLTranslationExceptionManager {
    
    private final LLkParser parser;
    private final String fileName;
    private final Position offsetPos;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public SLTranslationExceptionManager(LLkParser parser, 
                                         String fileName, 
                                         Position offsetPos) {
        this.parser    = parser;
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
    
    
    /**
     * Returns the  absolute source code position of the previous token.
     */
    private Position getPosition() {
        int line, column;
        try {
            line   = parser.LT(0).getLine();
            column = parser.LT(0).getColumn();
        } catch(Exception e) {
            line   = 1;
            column = 1;
        }
        return createAbsolutePosition(line, column);
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
    
    
    /**
     * Creates a string with the current absolute position information
     */
    public PositionedString createPositionedString(String text) {
        return new PositionedString(text, 
                                    fileName, 
                                    getPosition());
    }
    
    
    /**
     * Creates an SLTranslationException with current absolute position 
     * information.
     */
    public SLTranslationException createException(String message) {
        return new SLTranslationException(message, 
                                          fileName, 
                                          getPosition());
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
                                      getPosition());
    }
    
    public SLTranslationException createWarningException(String message, Token t) {
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
            pos = getPosition();
        }
        
        return new SLTranslationException(e.getMessage() 
                                          + " (" 
                                          + e.getClass().getName() 
                                          + ")", 
                                          fileName, 
                                          pos,
                                          e.getStackTrace());
    }
}
