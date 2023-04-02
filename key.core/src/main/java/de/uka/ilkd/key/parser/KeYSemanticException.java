package de.uka.ilkd.key.parser;

import javax.annotation.Nullable;
import java.net.MalformedURLException;

import de.uka.ilkd.key.util.RecognitionException;
import de.uka.ilkd.key.util.parsing.HasLocation;

import org.antlr.v4.runtime.CharStream;

public class KeYSemanticException extends RecognitionException implements HasLocation {
    private final String cat;
    private final String filename;

    public KeYSemanticException(CharStream input, String sourceName, String message) {
        super(input, null);
        this.cat = message;
        this.filename = sourceName;
    }

    public KeYSemanticException(CharStream input, String sourceName, Exception cause) {
        this(input, sourceName, cause.getMessage());
        initCause(cause);
    }

    public String getFilename() {
        return filename;
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
        return String.format("%s(%d, %d): %s", filename, getPosition().line(),
            getPosition().column(),
            getMessage());
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        return new Location(getFilename(), getPosition());
    }
}
