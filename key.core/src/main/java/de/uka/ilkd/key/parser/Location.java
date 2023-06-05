package de.uka.ilkd.key.parser;

import java.net.MalformedURLException;
import java.net.URL;
import java.util.Comparator;
import java.util.Objects;
import java.util.Optional;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.util.MiscTools;

import org.antlr.runtime.RecognitionException;
import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.Token;
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

public final class Location implements Comparable<Location> {
    /**
     * The location of the resource of the Location. May be null!
     */
    private final URL fileUrl;

    /**
     * The position in the file
     */
    private final Position position;

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
     * Legacy constructor for creating a new Location from a String denoting the file path and line
     * and column number, tries to convert the path given as String into a URL.
     *
     * @param filename path to the resource of the Location
     * @param position position of the Location
     * @throws RuntimeException if the given string is null or can not be parsed to URL
     * @deprecated Use {@link #Location(URL, Position)} instead.
     */
    @Deprecated
    public static Location fromFileName(String filename, Position position) {
        try {
            return new Location(filename == null ? null : MiscTools.parseURL(filename), position);
        } catch (MalformedURLException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * This factory method can be used to create a Location for a RecognitionException. A possibly
     * thrown MalformedURLException is caught and printed to debug output, null is returned instead.
     *
     * @param re the RecognitionException to create a Location for
     * @return the created Location or null if creation failed
     */
    public static Location create(RecognitionException re) {
        // ANTLR starts lines in column 0, files in line 1.
        return Location.fromFileName(re.input.getSourceName(),
            Position.fromOneZeroBased(re.line, re.charPositionInLine));
    }

    public static Location fromToken(Token token) {
        return Location.fromFileName(MiscTools.getFileNameFromTokenSource(token.getTokenSource()),
            Position.fromToken(token));
    }

    public Optional<URL> getFileURL() {
        return Optional.ofNullable(fileUrl);
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

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        Location location = (Location) o;
        return Objects.equals(fileUrl, location.fileUrl)
                && Objects.equals(position, location.position);
    }

    @Override
    public int hashCode() {
        return Objects.hash(fileUrl, position);
    }

    @Override
    public int compareTo(@Nonnull Location o) {
        return Comparator
                .<Location, String>comparing(l -> l.getFileURL().map(URL::toString).orElse(null))
                .thenComparing(Location::getPosition).compare(this, o);
    }
}
