/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.translation;

import java.net.MalformedURLException;
import java.net.URI;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.util.parsing.HasLocation;


public class SLTranslationException extends ProofInputException implements HasLocation {
    protected final Location location;

    public SLTranslationException(String message, Throwable cause, Location location) {
        super(message, cause);
        if (location == null) {
            throw new IllegalArgumentException();
        }
        this.location = location;
    }

    public SLTranslationException(String message, Location location, Throwable cause) {
        this(message, cause, location);
    }

    public SLTranslationException(String message, Location location) {
        this(message, null, location);
    }

    public SLTranslationException(String message) {
        this(message, null, new Location((URI) null, Position.UNDEFINED));
    }

    @Nullable
    @Override
    public Location getLocation() throws MalformedURLException {
        return location;
    }
}
