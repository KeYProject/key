/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.parsing;

import java.net.URI;
import java.util.Comparator;
import java.util.Objects;
import java.util.Optional;

import org.antlr.v4.runtime.IntStream;
import org.antlr.v4.runtime.Token;
import org.jspecify.annotations.NonNull;


/**
 * This class represents a location in a file. It consists of a filename, a line number and a column
 * number. The filename may be null, if the file is unknown (e.g. standard input). The class is
 * mainly used for parser exceptions.
 *
 * <p>
 * Both line and column numbers are assumed to be 1-based. That is the first character is on line 1,
 * column 1.
 *
 * @param fileUri The location of the resource of the Location. May be null!
 * @param position The position in the file
 * @author Hubert Schmid
 */
public record Location(URI fileUri, Position position) implements Comparable<Location> {
    public static final Location UNDEFINED = new Location(null, Position.UNDEFINED);

    public static Location fromToken(Token token) {
        return new Location(SourceNames.getURIFromTokenSource(token.getTokenSource()),
            Position.fromToken(token));
    }

    public URI getFileUri() { return fileUri; }

    /// @deprecated weigl: Usage of {@link Optional} is discourage.
    /// @see [#getFileUri()]
    @Deprecated
    public Optional<URI> getFileURI() { return Optional.ofNullable(fileUri); }

    public Position getPosition() { return position; }

    /**
     * Internal string representation. Do not rely on format!
     */
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
    public int hashCode() { return Objects.hash(fileUri, position); }

    @Override
    public int compareTo(@NonNull Location o) {
        return Comparator
                .<Location, URI>comparing(l -> l.fileUri,
                    Comparator.nullsLast(Comparator.naturalOrder()))
                .thenComparing(Location::getPosition,
                    Comparator.nullsLast(Comparator.naturalOrder()))
                .compare(this, o);
    }
}
