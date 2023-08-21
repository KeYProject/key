/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.net.MalformedURLException;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.Comparator;
import java.util.Objects;
import java.util.Optional;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.util.MiscTools;

import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.Token;


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
    @Nullable
    private final URI fileUri;

    /**
     * The position in the file
     */
    private final Position position;

    public static final Location UNDEFINED = new Location(null, Position.UNDEFINED);

    /**
     * Creates a new Location with the given resource location, line and column numbers.
     *
     * @param uri location of the resource
     * @param position position of the Location
     */
    public Location(URI uri, Position position) {
        this.fileUri = uri;
        this.position = position;
    }

    /**
     * Legacy constructor for creating a new Location from a String denoting the file path and line
     * and column number, tries to convert the path given as String into a URL.
     *
     * @param filename path to the resource of the Location
     * @param position position of the Location
     * @throws RuntimeException if the given string is null or can not be parsed to URL
     * @deprecated Use {@link #Location(URI, Position)} instead.
     */
    @Deprecated
    public static Location fromFileName(String filename, Position position) {
        try {
            return new Location(filename == null ? null : MiscTools.parseURL(filename).toURI(),
                position);
        } catch (MalformedURLException | URISyntaxException e) {
            throw new RuntimeException(e);
        }
    }

    public static Location fromToken(Token token) {
        return new Location(MiscTools.getURIFromTokenSource(token.getTokenSource()),
            Position.fromToken(token));
    }

    public Optional<URI> getFileURI() {
        return Optional.ofNullable(fileUri);
    }

    public Position getPosition() {
        return position;
    }

    /** Internal string representation. Do not rely on format! */
    @Override
    public String toString() {
        var url = fileUri == null ? IntStream.UNKNOWN_SOURCE_NAME : fileUri.toString();
        return "[" + url + ":" + position + "]";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        Location location = (Location) o;
        return Objects.equals(fileUri, location.fileUri)
                && Objects.equals(position, location.position);
    }

    @Override
    public int hashCode() {
        return Objects.hash(fileUri, position);
    }

    @Override
    public int compareTo(@Nonnull Location o) {
        return Comparator
                .<Location, URI>comparing(l -> l.fileUri)
                .thenComparing(Location::getPosition).compare(this, o);
    }
}
