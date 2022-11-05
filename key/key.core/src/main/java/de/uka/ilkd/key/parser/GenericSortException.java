package de.uka.ilkd.key.parser;

import org.antlr.runtime.RecognitionException;

import antlr.Token;
import de.uka.ilkd.key.logic.sort.Sort;

public class GenericSortException extends RecognitionException {
    /**
     *
     */
    private static final long serialVersionUID = 7887443025957191925L;
    String cat;
    String filename;
    Sort sort;
    String reason;

    public GenericSortException(String cat, String reason, Sort sort, Token t, String filename) {
        this.cat = cat;
        this.reason = reason;
        this.filename = filename;
        this.sort = sort;
        this.line = t.getLine();
        this.charPositionInLine = t.getColumn();
    }

    public GenericSortException(String cat, String reason, Sort sort, String filename, int line,
            int column) {
        this.cat = cat;
        this.reason = reason;
        this.filename = filename;
        this.sort = sort;
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
        String errmsg = cat + "\n  " + sort + "\n";
        return errmsg + reason;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return filename + "(" + this.line + ", " + this.charPositionInLine + "): " + getMessage();
    }
}
