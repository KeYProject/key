package de.uka.ilkd.key.parser;

import java.net.MalformedURLException;
import java.net.URL;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.util.MiscTools;

import org.antlr.runtime.RecognitionException;
import org.antlr.v4.runtime.IntStream;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * This class represents a location in a file. It consists of a filename, a line number and a column
 * number. The filename may be null, if the file is unknown (e.g. standard input). The class is
 * mainly used for parser exceptions.
 *
 * <p>
 * Both line and column numbers are assumed to be 1-based. That is the first character is on line 1,
 * column 1.
 *
 * @author Hubert Schmid
 */

public final class Location {
    private static final Logger LOGGER = LoggerFactory.getLogger(Location.class);

    /**
     * The location of the resource of the Location. May be null!
     */
    private final URL fileUrl;

    /**
     * The position in the file
     */
    private final Position position;

    /**
     * Legacy constructor for creating a new Location from a String denoting the file path and line
     * and column number, tries to convert the path given as String into a URL.
     *
     * @param filename path to the resource of the Location
     * @param position position of the Location
     * @throws MalformedURLException if the given string is null or can not be parsed to URL
     * @deprecated Use {@link #Location(URL, Position)} instead.
     */
    @Deprecated
    public Location(String filename, Position position) throws MalformedURLException {
        this(filename == null ? null : MiscTools.parseURL(filename), position);
    }

    /**
     * Creates a new Location with the given resource location, line and column numbers.
     *
     * @param url location of the resource
     * @param position position of the Location
     */
    public Location(URL url, Position position) {
        this.fileUrl = url;
        this.position = position;
    }

    /**
     * Creates a new Location with the given resource location, 1-based line and 0-based column
     * numbers.
     * This format is used by most parsers so this deserves an explicit method call.
     *
     * @param url location of the resource
     * @param line_1 1-based line of the Location
     * @param column_0 0-based column of the Location
     */
    public static Location newOneZeroBased(URL url, int line_1, int column_0) {
        return new Location(url, Position.fromOneZeroBased(line_1, column_0));
    }

    /**
     * This factory method can be used to create a Location for a RecognitionException. A possibly
     * thrown MalformedURLException is caught and printed to debug output, null is returned instead.
     *
     * @param re the RecognitionException to create a Location for
     * @return the created Location or null if creation failed
     */
    public static Location create(RecognitionException re) {
        try {
            // ANTLR starts lines in column 0, files in line 1.
            return new Location(re.input.getSourceName(),
                Position.fromOneZeroBased(re.line, re.charPositionInLine));
        } catch (MalformedURLException e) {
            LOGGER.error("Location could not be created from String: {}", re.input.getSourceName(),
                e);
            return null;
        }
    }

    /**
     * Checks if the given Location is valid, i.e. not null and has a URL.
     *
     * @param location the Location to check
     * @return true iff Location is valid
     */
    public static boolean isValidLocation(final Location location) {
        return !(location == null || location.getFileURL() == null);
    }

    public URL getFileURL() {
        return fileUrl;
    }

    public Position getPosition() {
        return position;
    }

    /** Internal string representation. Do not rely on format! */
    @Override
    public String toString() {
        var url = fileUrl == null ? IntStream.UNKNOWN_SOURCE_NAME : fileUrl.toString();
        return "[" + url + ":" + position + "]";
    }
}
