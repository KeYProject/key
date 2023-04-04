package de.uka.ilkd.key.parser;

import java.net.MalformedURLException;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;

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
        return cat;
    }

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
        return String.format("%s(%d, %d): %s", filename, this.getLine(), this.getColumn(),
            getMessage());
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        return new Location(getFilename(), Position.fromOneZeroBased(line, charPositionInLine));
    }
}
