/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;


import javax.annotation.Nullable;

import de.uka.ilkd.key.util.parsing.HasLocation;

/**
 * This class represents an error of a parser.
 *
 * @author Hubert Schmid
 */

public final class ParserException extends Exception implements HasLocation {
    /* --- constructors --- */
    /**
     * @param message The error message. The message may be shown to the user and should be
     *        appropriately formated.
     * @param location The location on which the error occured. The location may be null, if the
     *        location is unknown or the error is independent of a location.
     */
    public ParserException(String message, Location location) {
        super(message);
        this.location = location;
    }


    /* --- methods --- */

    /**
     * @return The location may be null.
     */
    @Nullable
    @Override
    public Location getLocation() {
        return location;
    }

    @Override
    public synchronized ParserException initCause(Throwable cause) {
        super.initCause(cause);
        return this;
    }

    /* --- fields --- */
    private final Location location;

}
