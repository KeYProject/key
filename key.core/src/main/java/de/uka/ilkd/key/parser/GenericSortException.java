package de.uka.ilkd.key.parser;

import de.uka.ilkd.key.logic.sort.Sort;

import antlr.Token;
import org.antlr.runtime.RecognitionException;

public class GenericSortException extends RecognitionException {
    /**
     *
     */
    private static final long serialVersionUID = 7887443025957191925L;
    final String cat;
    final String filename;
    final Sort sort;
    final String reason;

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
