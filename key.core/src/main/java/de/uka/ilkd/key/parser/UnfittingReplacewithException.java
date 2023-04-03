package de.uka.ilkd.key.parser;

import org.antlr.runtime.RecognitionException;

public class UnfittingReplacewithException extends RecognitionException {

    /**
     *
     */
    private static final long serialVersionUID = -497885048593588941L;
    private final String description;
    private final String filename;

    public UnfittingReplacewithException(String description, String filename, int line,
            int column) {
        super();
        this.filename = filename;
        this.line = line;
        this.charPositionInLine = column;
        this.description = description;
    }


    public String getMessage() {
        return (filename != null ? filename + ":" : "") + description;
    }

}
