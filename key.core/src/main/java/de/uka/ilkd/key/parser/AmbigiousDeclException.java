package de.uka.ilkd.key.parser;

import org.antlr.runtime.RecognitionException;

import antlr.Token;

public class AmbigiousDeclException extends RecognitionException {
    /**
     *
     */
    private static final long serialVersionUID = 5836342271644427009L;
    String filename = "unknown";
    String ambigious_symbol;
    Token t;

    public AmbigiousDeclException(String cat, Token t) {
        this.ambigious_symbol = t.getText();
        this.filename = t.getFilename();
        this.line = t.getLine();
        this.charPositionInLine = t.getColumn();
    }

    public AmbigiousDeclException(String ambigious_symbol, String filename, int line, int column) {
        this.filename = filename;
        this.ambigious_symbol = ambigious_symbol;
        this.line = line;
        this.charPositionInLine = column;
    }

    /**
     * Returns a clean error message (no line number/column information)
     *
     * @deprecated
     */
    @Deprecated
    public String getErrorMessage() {
        return getMessage();
    }

    /**
     * Returns a clean error message (no line number/column information)
     */
    public String getMessage() {
        return "The name \'" + ambigious_symbol + "\' is already in use.";
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return filename + "(" + this.line + ", " + this.charPositionInLine + "):\n" + getMessage();
    }
}
