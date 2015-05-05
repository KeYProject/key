package de.uka.ilkd.key.util;

import de.uka.ilkd.key.java.ParseExceptionInFile;
import de.uka.ilkd.key.parser.KeYSemanticException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.parser.proofjava.ParseException;
import de.uka.ilkd.key.parser.proofjava.Token;
import de.uka.ilkd.key.proof.SVInstantiationExceptionWithPosition;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;

/**
 * Various utility methods related to exceptions.
 * @author bruns
 * @since 2.4.0
 */
public final class ExceptionTools {

    /**
     * Tries to resolve the location (i.e., file name, line, and column)
     * from a parsing exception.
     * Result may be null.
     */
    public static Location getLocation(Throwable exc) {
        assert exc != null;
    
        Location location = null;
    
        if  (exc instanceof antlr.RecognitionException) { 
            location = new Location(((antlr.RecognitionException)exc).getFilename(),
                            ((antlr.RecognitionException) exc).getLine(),
                            ((antlr.RecognitionException) exc).getColumn());
        }
        else if  (exc instanceof org.antlr.runtime.RecognitionException) {
            org.antlr.runtime.RecognitionException recEx =
                            (org.antlr.runtime.RecognitionException) exc;
            // ANTLR 3 - Recognition Exception.
            String filename = "";
            if(exc instanceof KeYSemanticException) {
                filename = ((KeYSemanticException)exc).getFilename();
            } else if(recEx.input != null) {
                filename = recEx.input.getSourceName();
            }
    
            location = new Location(filename, recEx.line, recEx.charPositionInLine);
        }
        else if (exc instanceof ParserException) {
            location = ((ParserException) exc).getLocation();
        } else if (exc instanceof ParseExceptionInFile) {
            // This kind of exception has a filename but no line/col information
            // Retrieve the latter from the cause. location remains null if
            // no line/col is available in cause.
            if(exc.getCause() != null) {
                location = getLocation(exc.getCause());
                if(location != null) {
                    String filename = ((ParseExceptionInFile)exc).getFilename();
                    location = new Location(filename, location.getLine(), location.getColumn());
                }
            }
        } else if (exc instanceof ParseException) {
            ParseException pexc = (ParseException)exc;
            Token token = pexc.currentToken;
            if(token == null) {
                location = null;
            } else {
                location = new Location("", token.next.beginLine, token.next.beginColumn);
            }
        } else if (exc instanceof SLTranslationException) {
            SLTranslationException ste = (SLTranslationException) exc;
            location = new Location(ste.getFileName(), 
                            ste.getLine(), 
                            ste.getColumn());
        } else if (exc instanceof SVInstantiationExceptionWithPosition) {	      
            location = new Location(null, 
                            ((SVInstantiationExceptionWithPosition)exc).getRow(),
                            ((SVInstantiationExceptionWithPosition)exc).getColumn());
        } 
    
        if (location == null && exc.getCause() != null) {
            location = getLocation(exc.getCause());
        }
    
        return location;
    }

}
