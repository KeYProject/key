/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.parser;

import org.key_project.util.parsing.HasLocation;
import org.key_project.util.parsing.Location;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class represents an error of a parser.
 *
 * @author Hubert Schmid
 */

@NullMarked
public final class ParserException extends RuntimeException implements HasLocation {
    /* --- constructors --- */
    /**
     * @param message The error message. The message may be shown to the user and should be
     *        appropriately formated. The message may be null if no message is available.
     * @param location The location on which the error occured. The location may be null, if the
     *        location is unknown or the error is independent of a location.
     */
    public ParserException(@Nullable String message, @Nullable Location location) {
        super(message + " at " + location);
        this.location = location;
    }


    /* --- methods --- */

    /**
     * @return The location may be null.
     */
    @Override
    public @Nullable Location getLocation() {
        return location;
    }

    /**
     * The overridden declaration requires a non-null return type, but this implementation may
     * legitimately return {@code null}; and the base declaration's {@code @PolyInitialized}
     * receiver does not match this override's implicit {@code @Initialized} receiver. Both
     * differences are suppressed with scoped keys.
     */
    @SuppressWarnings({ "nullness:override.return.invalid", "nullness:override.receiver.invalid" })
    @Override
    public synchronized ParserException initCause(@Nullable Throwable cause) {
        super.initCause(cause);
        return this;
    }

    /* --- fields --- */
    private final @Nullable Location location;

}
