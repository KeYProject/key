package de.uka.ilkd.key.java;

import recoder.parser.ParseException;

/**
 * This exception extends recoder's {@link ParseException} by a filename.
 *
 * The filename is used to display the location of an error in the sources. Line
 * and column number are not stored here explicitly but retrieved from the
 * cause.
 *
 * @author mulbrich
 *
 */
 @SuppressWarnings("serial")
public class ParseExceptionInFile extends ParseException {

    private final String filename;

    public ParseExceptionInFile(String filename, String message, Throwable cause) {
        super("Error in file " + filename + ": " + message);
        this.filename = filename;
        initCause(cause);
    }

    public ParseExceptionInFile(String filename, Throwable cause) {
        this(filename, cause.getMessage(), cause);
    }

    public String getFilename() {
        return filename;
    }
}
