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

package de.uka.ilkd.key.speclang.translation;

import org.antlr.runtime.MismatchedTokenException;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.Parser;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.PositionedString;


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

   public SLTranslationExceptionManager(Parser parser, String fileName,
         Position offsetPos) {
      this.line = parser.input.LT(1).getLine();
      this.column = parser.input.LT(1).getCharPositionInLine();
      this.fileName = fileName;
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

    private Position createAbsolutePosition(final Position pos) {
	return this.createAbsolutePosition(pos.getLine(), pos.getColumn());
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
                                                           t.getCharPositionInLine()));
    }

    /**
     * Creates a string with position information from the given relative
     * position.
     *
     * @param text
     *            the {@link String}
     * @param pos
     *            the {@link Position}
     * @return <code>text</code> as {@link PositionedString} with absolute
     *         position in the current file
     */
    public PositionedString createPositionedString(final String text,
	    final Position pos) {
	return new PositionedString(text, fileName, createAbsolutePosition(pos));
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
                                                                 t.getCharPositionInLine()));
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

   /**
    * Create a message from a {@link RecognitionException}. This needs to be
    * done manually because antlr exceptions are not designed to provide error
    * messages, see: http://www.antlr3.org/api/ActionScript/org/antlr/runtime/
    * RecognitionException.html
    */
   private String createMessage(RecognitionException e, Position pos) {
      String message = e.getMessage();
      if (message != null) {
         return message;
      }
      else {
         /*
          * A sequence of "instanceof" cases can be defined here in order to
          * create custom error messages for all relevant exception types.
          */

         // Convert the error position into a string
         String errorPosition = pos.getLine() + ":" + pos.getColumn();
         String token = e.token != null ? "'" + e.token.getText() + "'" : "";

         if (e instanceof NoViableAltException) {
            return "No viable alternative at line " + errorPosition + " "
                  + token;
         }
         if (e instanceof MismatchedTokenException) {
            return "Mismatched token at line " + errorPosition + " " + token;
         }
         return "[" + e.getClass().getName()
               + "] Unspecified syntax error at line " + errorPosition + " "
               + token;
      }
   }

    /**
     * Converts an ANTLRException into an SLTranslationException with the same
     * message and stack trace, and with current absolute position information.
     */
   public SLTranslationException convertException(RecognitionException e) {
      // no conversion necessary if e is already a SLTranslationException
      if (e instanceof SLTranslationException) {
         return (SLTranslationException) e;
      }
      Position pos = createAbsolutePosition(e.line, e.charPositionInLine);
      String message = createMessage(e, pos);
      return new SLTranslationException(message, fileName, pos, e);
   }

    public SLTranslationException convertException(
	    String message, RecognitionException e) {
	Position pos;
	pos = createAbsolutePosition(e.line, e.charPositionInLine);

	return new SLTranslationException(message + " ("
		+ e.getClass().getName() + ")", fileName, pos,
		e);
    }
}