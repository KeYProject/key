package de.uka.ilkd.key.java;

import java.net.MalformedURLException;
import javax.annotation.Nullable;

import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.util.ExceptionTools;
import de.uka.ilkd.key.util.parsing.HasLocation;

import recoder.parser.ParseException;

/**
 * This exception extends recoder's {@link ParseException} by a filename.
 * <p>
 * The filename is used to display the location of an error in the sources. Line and column number
 * are not stored here explicitly but retrieved from the cause.
 *
 * @author mulbrich
 */
public class ParseExceptionInFile extends ParseException implements HasLocation {
    private static final long serialVersionUID = -4228093987853508329L;
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

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        // This kind of exception has a filename but no line/col information
        // Retrieve the latter from the cause. location remains null if
        // no line/col is available in cause.
        Location location = null;
        if (getCause() != null) {
            location = ExceptionTools.getLocation(getCause());
            if (location != null) {
                location = new Location(getFilename(), location.getPosition());
            }
        }
        return location;
    }
}
