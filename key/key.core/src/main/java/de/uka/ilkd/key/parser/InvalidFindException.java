package de.uka.ilkd.key.parser;

import org.antlr.runtime.RecognitionException;

public class InvalidFindException extends RecognitionException {

    /**
     *
     */
    private static final long serialVersionUID = 1699188390606912785L;
    private String description;
    private String filename;

    public InvalidFindException(String description, String filename, int line, int column) {
        this.filename = filename;
        this.line = line;
        this.charPositionInLine = column;
        this.description = description;
    }

    public String getMessage() {
        return (this.filename != null ? this.filename : "") + "(" + this.line + ", "
            + this.charPositionInLine + "):" + description;
    }

}
