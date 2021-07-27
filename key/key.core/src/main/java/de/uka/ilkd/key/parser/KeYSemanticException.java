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

import de.uka.ilkd.key.util.parsing.HasLocation;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;

import javax.annotation.Nullable;
import java.net.MalformedURLException;

public class KeYSemanticException extends RecognitionException implements HasLocation {
    private final String cat;
    private final String filename;
    
    public KeYSemanticException(String message) {
        this.cat = message;
        this.filename = "<unknown>";
    }

    public KeYSemanticException(TokenStream input, String sourceName, String message) {
        super(input);
        this.cat = message;
        this.filename = sourceName;
    }

    public KeYSemanticException(TokenStream input, String sourceName, Exception cause) {
        this(input, sourceName, cause.getMessage());
        initCause(cause);
    }

    public String getFilename() {
        return filename;
    }
    
    public int getLine() {
        return line;        
    }
    
    public int getColumn() {
        return charPositionInLine;
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
    public String getMessage ()
    {
	return cat;
    }
    
    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return String.format("%s(%d, %d): %s", filename, this.getLine(), this.getColumn(), getMessage());
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        return new Location(getFilename(), getLine(), getColumn() + 1);
    }
}